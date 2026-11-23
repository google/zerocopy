-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import TulipModel.Heap

/-!
# Higher-Order Store Computation Monad `M` and Guarded Recursion

Defines TULIP's store-passing monad `M A = SemTy.comp A` (`paper.tex:1673–1712`)
over `(w', TotHeap m w') → StepLift m (Σ w'' ≥ w', TotHeap j w'' × A_j w'')`,
together with:
- `M.ret`, `M.bind`, `M.seq`, `M.step`
- `M.get` (1 guarded step `ϑ`), `M.set` (0 steps), `M.new` (0 steps, `fresh = maxLoc + 1`)
- `M.rec` (guarded general-recursive functions `A → M B`) and `M.diverge` (`Ω`)
- `SemTy.fold` and `M.unfold` for guarded recursive types `μ α. body`
-/

namespace Tulip

/-- Functorial action `StepLift.map` over stage-indexed answer families. -/
noncomputable def StepLift.map : {n : Nat} → {X Y : (m : Nat) → m ≤ n → Type 1} →
    (∀ (m : Nat) (hm : m ≤ n), X m hm → Y m hm) →
    StepLift n X → StepLift n Y
  | 0,     _, _, f, Sum.inl x  => Sum.inl (f 0 (Nat.le_refl 0) x)
  | 0,     _, _, _, Sum.inr _  => Sum.inr PUnit.unit
  | m + 1, _, _, f, Sum.inl x  => Sum.inl (f (m + 1) (Nat.le_refl (m + 1)) x)
  | _ + 1, _, _, f, Sum.inr c' =>
      Sum.inr (StepLift.map (fun j hj x => f j (Nat.le_succ_of_le hj) x) c')

@[simp]
theorem StepLift.map_ret {n : Nat} {X Y : (m : Nat) → m ≤ n → Type 1}
    (f : ∀ (m : Nat) (hm : m ≤ n), X m hm → Y m hm) (x : X n (Nat.le_refl n)) :
    StepLift.map f (StepLift.ret x) = StepLift.ret (f n (Nat.le_refl n) x) := by
  cases n <;> rfl

@[simp]
theorem StepLift.map_stepZero {X Y : (m : Nat) → m ≤ 0 → Type 1}
    (f : ∀ (m : Nat) (hm : m ≤ 0), X m hm → Y m hm) :
    StepLift.map f (StepLift.stepZero (X := X)) = StepLift.stepZero := rfl

@[simp]
theorem StepLift.map_stepSucc {n : Nat} {X Y : (m : Nat) → m ≤ n + 1 → Type 1}
    (f : ∀ (m : Nat) (hm : m ≤ n + 1), X m hm → Y m hm)
    (c : StepLift n (fun m hm => X m (Nat.le_succ_of_le hm))) :
    StepLift.map f (StepLift.stepSucc c) =
      StepLift.stepSucc (StepLift.map (fun j hj x => f j (Nat.le_succ_of_le hj) x) c) := rfl

@[simp]
theorem StepLift.map_id {n : Nat} {X : (m : Nat) → m ≤ n → Type 1}
    (c : StepLift n X) :
    StepLift.map (fun _ _ x => x) c = c := by
  induction n with
  | zero =>
    cases c with
    | inl _ => rfl
    | inr u => cases u; rfl
  | succ m ih =>
    cases c with
    | inl _ => rfl
    | inr c' => exact congrArg Sum.inr (ih c')

theorem StepLift.map_map {n : Nat} {X Y Z : (m : Nat) → m ≤ n → Type 1}
    (f : ∀ (m : Nat) (hm : m ≤ n), X m hm → Y m hm)
    (g : ∀ (m : Nat) (hm : m ≤ n), Y m hm → Z m hm)
    (c : StepLift n X) :
    StepLift.map g (StepLift.map f c) =
      StepLift.map (fun m hm x => g m hm (f m hm x)) c := by
  induction n with
  | zero => cases c <;> rfl
  | succ m ih =>
    cases c with
    | inl _ => rfl
    | inr c' => exact congrArg Sum.inr (ih _ _ c')

theorem StepLift.bind_map {n : Nat} {X Y Z : (m : Nat) → m ≤ n → Type 1}
    (f : ∀ (m : Nat) (hm : m ≤ n), X m hm → Y m hm)
    (c : StepLift n X)
    (k : ∀ (m : Nat) (hm : m ≤ n), Y m hm → StepLift m (fun j hj => Z j (Nat.le_trans hj hm))) :
    StepLift.bind (StepLift.map f c) k =
      StepLift.bind c (fun m hm x => k m hm (f m hm x)) := by
  induction n with
  | zero => cases c <;> rfl
  | succ m ih =>
    cases c with
    | inl _ => rfl
    | inr c' => exact congrArg Sum.inr (ih _ c' _)

theorem StepLift.map_bind {n : Nat} {X Y Z : (m : Nat) → m ≤ n → Type 1}
    (c : StepLift n X)
    (k : ∀ (m : Nat) (hm : m ≤ n), X m hm → StepLift m (fun j hj => Y j (Nat.le_trans hj hm)))
    (g : ∀ (m : Nat) (hm : m ≤ n), Y m hm → Z m hm) :
    StepLift.map g (StepLift.bind c k) =
      StepLift.bind c (fun m hm x =>
        StepLift.map (fun j hj y => g j (Nat.le_trans hj hm) y) (k m hm x)) := by
  induction n with
  | zero => cases c <;> rfl
  | succ m ih =>
    cases c with
    | inl _ => rfl
    | inr c' => exact congrArg Sum.inr (ih c' _ _)

@[simp]
theorem StepLift.lLift_map {n : Nat} {X Y : (m : Nat) → m ≤ n → Type 1}
    (f : ∀ (m : Nat) (hm : m ≤ n), X m hm → Y m hm)
    (c : StepLift n X) (Φ : ∀ (m : Nat) (hm : m ≤ n), Y m hm → Prop) :
    StepLift.lLift (StepLift.map f c) Φ =
      StepLift.lLift c (fun m hm x => Φ m hm (f m hm x)) := by
  induction n with
  | zero => cases c <;> rfl
  | succ m ih =>
    cases c with
    | inl _ => rfl
    | inr c' => exact ih _ c' _

/-! ## Base `SemTy` Combinators and Store Monad `M` -/

abbrev SemTy.unit : SemTy := .const PUnit
abbrev SemTy.nat  : SemTy := .const Nat
abbrev SemTy.bool : SemTy := .const Bool

/-- Higher-order store computation monad `M A = SemTy.comp A`. -/
abbrev M (A : SemTy) : SemTy := .comp A

namespace M

/-- Re-anchor the world-extension witness in a `CompAns` bundle from `w₂` back to `w₁`
along `hw12 : World.Le (w₁.restrict hj) w₂`. -/
noncomputable def reanchorAns {A : SemTy} {m j : Nat} {w₁ : World m} {w₂ : World j}
    (hj : j ≤ m) (hw12 : World.Le (w₁.restrict hj) w₂)
    (q : Nat) (hq : q ≤ j) (ans : CompAns A j w₂ q hq) :
    CompAns A m w₁ q (Nat.le_trans hq hj) :=
  ⟨ans.1,
   ⟨by
     have hsub : World.Le ((w₁.restrict hj).restrict hq) (w₂.restrict hq) :=
       World.restrict_mono hq hw12
     rw [World.restrict_trans] at hsub
     exact World.le_trans hsub ans.2.1.proof⟩,
   ans.2.2.1,
   ans.2.2.2⟩

/-- Monadic return `ret a : M A` (0 steps, world and heap unchanged). -/
noncomputable def ret {n : Nat} {A : SemTy} {w : World n} (a : SemTy.eval n A w) :
    SemTy.eval n (M A) w :=
  fun _ hm w' hw' h =>
    StepLift.ret ⟨w', ⟨by simpa using World.le_refl w'⟩, h, SemTy.map hw' (SemTy.restrict hm a)⟩

/-- Monadic bind `x ← e; k x` for `e : M A` and Kripke continuation `k : A → M B`. -/
noncomputable def bind {n : Nat} {A B : SemTy} {w : World n}
    (e : SemTy.eval n (M A) w) (k : SemTy.eval n (.arr A (M B)) w) :
    SemTy.eval n (M B) w :=
  fun m hm w' hw' h =>
    StepLift.bind (e m hm w' hw' h) (fun j hj ans =>
      let w'' := ans.1
      let hw'' : World.Le (w'.restrict hj) w'' := ans.2.1.proof
      let h'' := ans.2.2.1
      let a   := ans.2.2.2
      have hw_w'' : World.Le (w.restrict (Nat.le_trans hj hm)) w'' := by
        rw [← World.restrict_trans hj hm w]
        exact World.le_trans (World.restrict_mono hj hw') hw''
      StepLift.map (reanchorAns hj hw'')
        (k j (Nat.le_trans hj hm) w'' hw_w'' a j (Nat.le_refl j) w''
          (by simpa using World.le_refl w'') h''))

/-- Sequential composition `e₁ ;; e₂` discarding `e₁`'s result. -/
noncomputable def seq {n : Nat} {A B : SemTy} {w : World n}
    (e₁ : SemTy.eval n (M A) w) (e₂ : SemTy.eval n (M B) w) :
    SemTy.eval n (M B) w :=
  bind e₁ (fun _ hm' _ hw'' _ => SemTy.map hw'' (SemTy.restrict hm' e₂))

/-- Guarded computation tick `step : M ()` (`paper.tex:314`), advancing one stage. -/
noncomputable def step {n : Nat} {w : World n} : SemTy.eval n (M SemTy.unit) w :=
  fun m _ w' _ h =>
    match m, w', h with
    | 0,     _,  _ => StepLift.stepZero
    | _ + 1, w', h =>
        StepLift.stepSucc
          (StepLift.ret ⟨w'.trunc, ⟨World.le_refl w'.trunc⟩, TotHeap.trunc h, ⟨PUnit.unit⟩⟩)

/-- Reference read `get r : M A` (`paper.tex:1704–1711`), taking 1 guarded step `ϑ`! -/
noncomputable def get {n : Nat} {A : SemTy} {w : World n} (r : SemTy.eval n (.ref A) w) :
    SemTy.eval n (M A) w :=
  fun m hm w' hw' h =>
    match m, hm, w', hw', h with
    | 0,     _,  _,  _,   _ => StepLift.stepZero
    | k + 1, hm, w', hw', h =>
        have hl_restr : (w.restrict hm).cells r.down.1 = some A := by
          cases n with
          | zero => omega
          | succ q =>
            have hr : w.cells r.down.1 = some A := r.down.2
            simp [World.restrict_cells, hr, LaterTy.restrict]
        have hl' : w'.cells r.down.1 = some A := hw' r.down.1 A hl_restr
        let a_k : SemTy.eval k A w'.trunc := CellVal.toEval (h.get r.down.1 A hl')
        StepLift.stepSucc
          (StepLift.ret ⟨w'.trunc, ⟨World.le_refl w'.trunc⟩, TotHeap.trunc h, a_k⟩)

/-- Reference write `set r a : M ()` (`paper.tex:1693–1700`), taking **0** steps! -/
noncomputable def set {n : Nat} {A : SemTy} {w : World n}
    (r : SemTy.eval n (.ref A) w) (a : SemTy.eval n A w) :
    SemTy.eval n (M SemTy.unit) w :=
  fun m hm w' hw' h =>
    have hl_restr : (w.restrict hm).cells r.down.1 = some (SemTy.nextAt m A) := by
      simp [World.restrict_cells, r.down.2]
    have hl' : w'.cells r.down.1 = some (SemTy.nextAt m A) :=
      hw' r.down.1 (SemTy.nextAt m A) hl_restr
    let a' : SemTy.eval m A w' := SemTy.map hw' (SemTy.restrict hm a)
    let h' : TotHeap m w' := TotHeap.update h r.down.1 hl' (CellVal.nextVal a')
    StepLift.ret ⟨w', ⟨by simpa using World.le_refl w'⟩, h', ⟨PUnit.unit⟩⟩

/-- Reference allocation `new a : M (ref A)` (`paper.tex:308`), taking **0** steps
and deterministically choosing `fresh w' = maxLoc w' + 1`! -/
noncomputable def new {n : Nat} {A : SemTy} {w : World n} (a : SemTy.eval n A w) :
    SemTy.eval n (M (.ref A)) w :=
  fun m hm w' hw' h =>
    let l_new := w'.fresh
    let T_m   := SemTy.nextAt m A
    let w''   := w'.insert l_new T_m
    have hle : World.Le w' w'' := World.le_insert_fresh w' T_m
    let a'' : SemTy.eval m A w'' :=
      SemTy.map (World.le_trans hw' hle) (SemTy.restrict hm a)
    let h'' : TotHeap m w'' := TotHeap.alloc h (CellVal.nextVal a'')
    have hl'' : w''.cells l_new = some T_m := by simp [w'']
    StepLift.ret ⟨w'', ⟨by simpa using hle⟩, h'', ⟨⟨l_new, hl''⟩⟩⟩

/-- Guarded recursive function `rec f x => body f x` (`paper.tex:813–822`) at `(n, w)`
from a world-polymorphic body `body : (A → M B) → (A → M B)`, satisfying
`recFn body x ≡ step ;; body (recFn body) x`. -/
noncomputable def recFn {n : Nat} {A B : SemTy} {w : World n}
    (body : SemTy.eval n (.arr (.arr A (M B)) (.arr A (M B))) w) :
    SemTy.eval n (.arr A (M B)) w :=
  let rec loop : (p : Nat) → (hp : p ≤ n) → (wp : World p) →
      World.Le (w.restrict hp) wp → SemTy.eval p (.arr A (M B)) wp
    | 0,     _,  _,  _   => fun m hm _ _ _ j hj w₂ _ _ =>
        match m, hm, j, hj, w₂ with
        | 0, _, 0, _, _ => StepLift.stepZero
    | k + 1, hp, wp, hwp => fun m hm w' hw' a j hj w₂ hw₂ h₂ =>
        match j, hj, w₂, hw₂, h₂ with
        | 0,     _,  _,  _,   _  => StepLift.stepZero
        | q + 1, hj, w₂, hw₂, h₂ =>
            have hq_le_k : q ≤ k := Nat.le_of_succ_le_succ (Nat.le_trans hj hm)
            have hq_le_n : q ≤ n := Nat.le_trans (Nat.le_succ_of_le hq_le_k) hp
            have hw_trunc : World.Le (w.restrict hq_le_n) w₂.trunc := by
              have heq : w.restrict hq_le_n =
                  (((w.restrict hp).restrict hm).restrict hj).trunc := by
                simp [World.trunc]
              rw [heq]
              exact World.restrict_mono _
                (World.le_trans (World.restrict_mono hj
                  (World.le_trans (World.restrict_mono hm hwp) hw')) hw₂)
            let self_q := loop q hq_le_n w₂.trunc hw_trunc
            let a_q := SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl q))
              (SemTy.map hw₂ (SemTy.restrict hj a))
            StepLift.stepSucc
              (StepLift.map
                (reanchorAns (Nat.le_succ_of_le (Nat.le_refl q)) (World.le_refl w₂.trunc))
                (body q hq_le_n w₂.trunc hw_trunc self_q
                  q (Nat.le_refl q) w₂.trunc (by simpa using World.le_refl w₂.trunc) a_q
                  q (Nat.le_refl q) w₂.trunc (by simpa using World.le_refl w₂.trunc)
                  (TotHeap.trunc h₂)))
  loop n (Nat.le_refl n) w (by simpa using World.le_refl w)

/-- Diverging computation `Ω : M A` (`gfix step`), stepping forever at every stage. -/
noncomputable def diverge {n : Nat} {A : SemTy} {w : World n} : SemTy.eval n (M A) w :=
  let rec go : (m : Nat) → (w' : World m) → StepLift m (CompAns A m w')
    | 0,     _  => StepLift.stepZero
    | k + 1, w' =>
        StepLift.stepSucc
          (StepLift.map (reanchorAns (Nat.le_succ_of_le (Nat.le_refl k)) (World.le_refl w'.trunc))
            (go k w'.trunc))
  fun m _ w' _ _ => go m w'

end M

/-! ## Guarded Recursive Type `fold` and `unfold` (`paper.tex:273–283, 330–348`) -/

/-- `fold u : μ body` for `u : body[μ body / 0]` (pure constructor, 0 steps). -/
noncomputable def SemTy.fold {n : Nat} {body : SemTy} {w : World n}
    (u : SemTy.eval n (body.subst0 (.mu body)) w) :
    SemTy.eval n (.mu body) w :=
  match n, w, u with
  | 0,     _, _ => PUnit.unit
  | k + 1, _, u =>
      CellVal.ofEval (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl k)) u)

/-- `unfold u : M (body[μ body / 0])` for `u : μ body` (1 guarded step `ϑ`). -/
noncomputable def M.unfold {n : Nat} {body : SemTy} {w : World n}
    (u : SemTy.eval n (.mu body) w) :
    SemTy.eval n (M (body.subst0 (.mu body))) w :=
  fun m hm w' hw' h =>
    match m, hm, w', hw', h with
    | 0,     _,  _,  _,   _ => StepLift.stepZero
    | k + 1, hm, w', hw', h =>
        let u' : SemTy.eval (k + 1) (.mu body) w' := SemTy.map hw' (SemTy.restrict hm u)
        StepLift.stepSucc
          (StepLift.ret ⟨w'.trunc, ⟨World.le_refl w'.trunc⟩, TotHeap.trunc h,
            CellVal.toEval u'⟩)

end Tulip
