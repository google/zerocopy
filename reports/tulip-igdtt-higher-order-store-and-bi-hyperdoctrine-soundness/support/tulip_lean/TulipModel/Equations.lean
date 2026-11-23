-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import TulipModel.WP

/-!
# Equational Theory of Higher-Order Store, Tightness Counterexamples & Divergence

Proves inside TULIP's step-indexed world/heaplet model (`paper.tex:296–360, 740–825`):

1. **Zero-step equational congruence (`wp_congr`, `wp_bind_congr`)**: semantic
   equality `e₁ = e₂` in `M A` rewrites directly inside `wpRepaired` (including
   under Kripke continuations) without consuming `▷` steps.
2. **Positive equational laws (`=` in `SemTy.eval n (M A) w`)**:
   - Monad laws: `bind_ret_left_at`, `bind_ret_left`, `bind_ret_right`, `bind_assoc`
   - Store interaction laws:
     - `get_after_set`: `set r v ;; get r = step ;; set r v ;; ret v` (1 step)
     - `set_after_new`: `r ← new u; set r v ;; k r = r ← new v; k r` (**0** steps!)
     - `set_after_set`: `set r u ;; set r v = set r v` (**0** steps!)
     - `get_after_get_comm`: `(x ← get r₁; y ← get r₂; k x y) = (y ← get r₂; x ← get r₁; k x y)`
     - `set_after_get` & `set_after_get_unit`: `(x ← get r; set r x ;; k x) = (x ← get r; k x)`
       and `(x ← get r; set r x) = step`
   - Recursive type laws: `unfold_of_fold` and `fold_of_unfold`
3. **Negative tightness counterexamples (`≠`)**:
   - `not_get_after_set_nostep`: `set r v ;; get r ≠ set r v ;; ret v`
   - `not_diagonal_get_idempotent`: `(x ← get r; y ← get r; ret (x, y)) ≠ (x ← get r; ret (x, x))`
   - `not_dead_new_elim`: `(new 0 ;; ret ()) ≠ ret ()`
   - `not_new_comm`: `(r ← new 10; s ← new 20; ret (r, s)) ≠ (s ← new 20; r ← new 10; ret (r, s))`
4. **Partial-correctness divergence witness (`diverge_wp_false`)**:
   `⊤ ⊢ wpRepaired M.diverge (fun _ => ⊥)` at all stages `n` and worlds `w`.
-/

namespace Tulip

/-! ## Zero-Step Equational Congruence Inside `wpRepaired` -/

/-- Semantic equality `e₁ = e₂` of computations rewrites inside `wpRepaired` with
**zero** `▷` cost (`paper.tex:730–738`). -/
theorem wp_congr {n : Nat} {w : World n} {A : SemTy}
    {e₁ e₂ : SemTy.eval n (M A) w} (heq : e₁ = e₂) (Φ : BIPred n w A) :
    wpRepaired e₁ Φ = wpRepaired e₂ Φ := by
  rw [heq]

/-- Congruence under Kripke continuations: pointwise equality of `k₁` and `k₂`
yields `M.bind e k₁ = M.bind e k₂` and hence identical `wpRepaired`. -/
theorem wp_bind_congr {n : Nat} {w : World n} {A B : SemTy}
    (e : SemTy.eval n (M A) w) {k₁ k₂ : SemTy.eval n (.arr A (M B)) w}
    (hk : ∀ m hm w' hw' a, k₁ m hm w' hw' a = k₂ m hm w' hw' a)
    (Φ : BIPred n w B) :
    wpRepaired (M.bind e k₁) Φ = wpRepaired (M.bind e k₂) Φ := by
  have hk_eq : k₁ = k₂ := by
    funext m hm w' hw' a
    exact hk m hm w' hw' a
  rw [hk_eq]

/-! ## Helper Identities on Applied `SemTy.map`/`restrict`, `M.reanchorAns` & Cell Reads -/

@[simp]
theorem SemTy.eval_comp_map_restrict {n m j : Nat} {A : SemTy}
    {w : World n} {w' : World m} {w₂ : World j}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w')
    (c : SemTy.eval n (M A) w)
    (hj : j ≤ m) (hw₂ : World.Le (w'.restrict hj) w₂) (h : TotHeap j w₂) :
    (SemTy.map hw' (SemTy.restrict hm c)) j hj w₂ hw₂ h =
      c j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) h := by
  unfold SemTy.map
  unfold SemTy.restrict
  rfl

@[simp]
theorem SemTy.eval_arr_map_restrict {n m j : Nat} {A B : SemTy}
    {w : World n} {w' : World m} {w₂ : World j}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w')
    (f : SemTy.eval n (.arr A B) w)
    (hj : j ≤ m) (hw₂ : World.Le (w'.restrict hj) w₂) (a : SemTy.eval j A w₂) :
    (SemTy.map hw' (SemTy.restrict hm f)) j hj w₂ hw₂ a =
      f j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) a := by
  unfold SemTy.map
  unfold SemTy.restrict
  rfl

@[simp]
theorem M.reanchorAns_refl {A : SemTy} {m : Nat} {w : World m}
    (hw : World.Le (w.restrict (Nat.le_refl m)) w)
    (q : Nat) (hq : q ≤ m) (ans : CompAns A m w q hq) :
    M.reanchorAns (Nat.le_refl m) hw q hq ans = ans := by
  rcases ans with ⟨w'', ⟨hw''⟩, h'', a⟩
  rfl

@[simp]
theorem M.reanchorAns_comp {A : SemTy} {m j q r : Nat}
    {w₁ : World m} {w₂ : World j} {w₃ : World q}
    (hj : j ≤ m) (hw12 : World.Le (w₁.restrict hj) w₂)
    (hq : q ≤ j) (hw23 : World.Le (w₂.restrict hq) w₃)
    (hr : r ≤ q) (ans : CompAns A q w₃ r hr) :
    M.reanchorAns hj hw12 r (Nat.le_trans hr hq) (M.reanchorAns hq hw23 r hr ans) =
      M.reanchorAns (Nat.le_trans hq hj) (World.step_le_trans hq hj hw12 hw23) r hr ans := by
  rcases ans with ⟨w'', ⟨hw''⟩, h'', a⟩
  rfl

/-- Reading a cell from `TotHeap.trunc h` at stage `k + 1` agrees with reading at
stage `k + 2` and restricting the semantic value to stage `k`. -/
theorem TotHeap.toEval_trunc_get {k : Nat} {w : World (k + 2)} {A : SemTy}
    (h : TotHeap (k + 2) w) (l : Loc)
    (hl : w.cells l = some A)
    (hl_tr : w.trunc.cells l = some A) :
    CellVal.toEval ((TotHeap.trunc h).get l A hl_tr) =
      SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl k))
        (CellVal.toEval (h.get l A hl)) := by
  simp only [TotHeap.trunc, Heaplet.restrict, CellVal.restrict, CellVal.toEval_ofEval]
  have htr_refl : World.trunc_restrict_le (Nat.le_succ_of_le (Nat.le_refl (k + 1))) w =
      World.le_refl w.trunc.trunc := rfl
  rw [htr_refl, SemTy.map_refl]

/-- Writing back the exact value just read from `h` at stage `k + 1` produces the
identical truncated cell value in `TotHeap.trunc h`. -/
theorem TotHeap.nextVal_toEval_eq_trunc_get {k : Nat} {w : World (k + 1)} {A : SemTy}
    (h : TotHeap (k + 1) w) (l : Loc)
    (hl : w.cells l = some A)
    (hl_tr : w.trunc.cells l = some (SemTy.nextAt k A)) :
    CellVal.nextVal (CellVal.toEval (h.get l A hl)) =
      (TotHeap.trunc h).get l (SemTy.nextAt k A) hl_tr := by
  cases k with
  | zero => rfl
  | succ q =>
    simp only [CellVal.nextVal, TotHeap.trunc, Heaplet.restrict, CellVal.restrict, SemTy.nextAt]
    have htr_refl : World.trunc_restrict_le (Nat.le_succ_of_le (Nat.le_refl (q + 1))) w =
        World.le_refl w.trunc.trunc := rfl
    rw [htr_refl, SemTy.map_refl]

/-! ## Positive Monad Laws (`bind_ret_left`, `bind_ret_right`, `bind_assoc`) -/

/-- Pointwise left-unit law for `M.bind (M.ret a) k` (valid for ANY continuation `k`). -/
theorem bind_ret_left_at {n : Nat} {w : World n} {A B : SemTy}
    (a : SemTy.eval n A w) (k : SemTy.eval n (.arr A (M B)) w)
    (m : Nat) (hm : m ≤ n) (w' : World m) (hw' : World.Le (w.restrict hm) w')
    (h : TotHeap m w') :
    M.bind (M.ret a) k m hm w' hw' h =
      k m hm w' hw' (SemTy.map hw' (SemTy.restrict hm a))
        m (Nat.le_refl m) w' (by simpa using World.le_refl w') h := by
  dsimp only [M.bind, M.ret]
  rw [StepLift.bind_ret]
  have hid : (M.reanchorAns (A := B) (Nat.le_refl m) (by simpa using World.le_refl w')) =
      (fun _ _ ans => ans) := by
    funext q hq ans
    exact M.reanchorAns_refl _ q hq ans
  rw [hid, StepLift.map_id]

/-- Full monadic left-unit law `M.bind (M.ret a) k = k a` for any natural continuation `k`. -/
theorem bind_ret_left {n : Nat} {w : World n} {A B : SemTy}
    (a : SemTy.eval n A w) (k : SemTy.eval n (.arr A (M B)) w)
    (hnat : IsNaturalCont k) :
    M.bind (M.ret a) k =
      k n (Nat.le_refl n) w (by simpa using World.le_refl w) a := by
  funext m hm w' hw' h
  rw [bind_ret_left_at]
  have hk_eq := hnat hm (Nat.le_refl n) (World.restrict_refl_le w) hw' a
  rw [← hk_eq, SemTy.eval_comp_map_restrict]

/-- Monadic right-unit law `(x ← e; ret x) = e` (holds unconditionally for ALL `e`!). -/
theorem bind_ret_right {n : Nat} {w : World n} {A : SemTy}
    (e : SemTy.eval n (M A) w) :
    M.bind e (fun _ _ _ _ x => M.ret x) = e := by
  funext m hm w' hw' h
  dsimp only [M.bind, M.ret]
  refine (congrArg (StepLift.bind (e m hm w' hw' h)) ?_).trans (StepLift.bind_ret_right _)
  funext j hj ans
  rw [StepLift.map_ret]
  rcases ans with ⟨w'', ⟨hw''⟩, h'', a⟩
  dsimp only [M.reanchorAns]
  rw [SemTy.restrict_refl_map (World.restrict_refl_le w'') a]

/-- Monadic associativity law `(y ← (x ← e; k₁ x); k₂ y) = (x ← e; y ← k₁ x; k₂ y)`
(holds unconditionally for ALL `e, k₁, k₂`!). -/
theorem bind_assoc {n : Nat} {w : World n} {A B C : SemTy}
    (e : SemTy.eval n (M A) w)
    (k₁ : SemTy.eval n (.arr A (M B)) w)
    (k₂ : SemTy.eval n (.arr B (M C)) w) :
    M.bind (M.bind e k₁) k₂ =
      M.bind e (fun m hm w' hw' a =>
        M.bind (k₁ m hm w' hw' a) (SemTy.map hw' (SemTy.restrict hm k₂))) := by
  funext m hm w' hw' h
  dsimp only [M.bind]
  rw [StepLift.bind_assoc]
  congr 1
  funext j hj ans₁
  rw [StepLift.bind_map, StepLift.map_bind]
  congr 1
  funext q hq ans₂
  rw [StepLift.map_map, SemTy.eval_arr_map_restrict]
  dsimp only [M.reanchorAns]
  congr 1

/-! ## Positive Higher-Order Store Interaction Laws (`paper.tex:319–327`) -/

/-- **`get_after_set` (`paper.tex:322`)**:
`set r v ;; get r = step ;; set r v ;; ret v` (1 guarded step `step` from `get`). -/
theorem get_after_set {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) (v : SemTy.eval n A w) :
    M.seq (M.set r v) (M.get r) =
      M.seq M.step (M.seq (M.set r v) (M.ret v)) := by
  rcases r with ⟨⟨l, hl⟩⟩
  funext m hm w' hw' h
  cases m with
  | zero =>
    simp [M.seq, M.bind, M.set, M.get, M.step]
  | succ k =>
    cases n with
    | zero => omega
    | succ n₀ =>
      have hl' : w'.cells l = some A :=
        hw' l A (by simp [World.restrict_cells, hl, SemTy.nextAt, LaterTy.restrict])
      simp only [M.seq, M.bind, M.set, M.get, M.step, M.ret,
        SemTy.eval_comp_map_restrict, StepLift.bind_ret, StepLift.bind_stepSucc,
        StepLift.map_stepSucc, StepLift.map_ret]
      congr 2
      dsimp only [M.reanchorAns]
      let hk_le : k ≤ k + 1 := Nat.le_succ_of_le (Nat.le_refl k)
      have hv_rhs :
          SemTy.map (World.step_le_trans (Nat.le_refl k)
              (Nat.le_trans hk_le hm)
              (World.step_le_trans hk_le hm hw' (World.le_refl w'.trunc))
              (World.restrict_refl_le w'.trunc))
            (SemTy.restrict (Nat.le_trans (Nat.le_refl k) (Nat.le_trans hk_le hm)) v) =
          SemTy.restrict hk_le (SemTy.map hw' (SemTy.restrict hm v)) := by
        rw [SemTy.restrict_map_comm hk_le hw' (SemTy.restrict hm v),
          ← SemTy.restrict_trans_map hk_le hm (World.restrict_trans_le hk_le hm w) v,
          SemTy.map_trans]
      have hh_eq :
          TotHeap.trunc (TotHeap.update (A := A) h l hl'
            (CellVal.nextVal (SemTy.map hw' (SemTy.restrict hm v)))) =
          TotHeap.update (A := A) (TotHeap.trunc h) l
            (by cases k <;> simp [World.trunc, World.restrict_cells, SemTy.nextAt, LaterTy.restrict, hl'])
            (CellVal.nextVal
              (SemTy.map (World.step_le_trans (Nat.le_refl k)
                  (Nat.le_trans hk_le hm)
                  (World.step_le_trans hk_le hm hw' (World.le_refl w'.trunc))
                  (World.restrict_refl_le w'.trunc))
                (SemTy.restrict (Nat.le_trans (Nat.le_refl k) (Nat.le_trans hk_le hm)) v))) := by
        rw [hv_rhs, TotHeap.trunc_update]
      have ha_eq :
          CellVal.toEval ((TotHeap.update (A := A) h l hl'
            (CellVal.nextVal (SemTy.map hw' (SemTy.restrict hm v)))).get l A hl') =
          SemTy.map (World.step_le_trans (Nat.le_refl k)
              (Nat.le_trans hk_le hm)
              (World.step_le_trans hk_le hm hw' (World.le_refl w'.trunc))
              (World.restrict_refl_le w'.trunc))
            (SemTy.restrict (Nat.le_trans (Nat.le_refl k) (Nat.le_trans hk_le hm)) v) := by
        rw [hv_rhs]
        simp [TotHeap.update, CellVal.nextVal]
      congr 2
      exact Prod.ext hh_eq ha_eq

/-- **`set_after_new` (`paper.tex:323`, **0 steps!**)**:
`r ← new u; set r v ;; k r = r ← new v; k r`. -/
theorem set_after_new {n : Nat} {w : World n} {A B : SemTy}
    (u v : SemTy.eval n A w) (k : SemTy.eval n (.arr (.ref A) (M B)) w) :
    M.bind (M.new u) (fun m hm w' hw' r =>
        M.seq (M.set r (SemTy.map hw' (SemTy.restrict hm v))) (k m hm w' hw' r)) =
      M.bind (M.new v) k := by
  funext m hm w' hw' h
  simp only [M.bind, M.seq, M.new, M.set, SemTy.eval_comp_map_restrict,
    StepLift.bind_ret, StepLift.map_map, SemTy.restrict_refl_map, TotHeap.alloc_update_fresh]
  dsimp only [M.reanchorAns]
  congr 1

/-- **`set_after_set` (`paper.tex:324`, **0 steps!**)**:
`set r u ;; set r v = set r v`. -/
theorem set_after_set {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) (u v : SemTy.eval n A w) :
    M.seq (M.set r u) (M.set r v) = M.set r v := by
  rcases r with ⟨⟨l, hl⟩⟩
  funext m hm w' hw' h
  simp only [M.seq, M.bind, M.set, SemTy.eval_comp_map_restrict,
    StepLift.bind_ret, StepLift.map_ret]
  congr 1
  dsimp only [M.reanchorAns]
  congr 2
  exact Prod.ext (by rw [TotHeap.update_update]) rfl

/-- **`get_after_get_comm` (`paper.tex:325`)**:
Two consecutive reads commute even when `r₁` and `r₂` may alias! -/
theorem get_after_get_comm {n : Nat} {w : World n} {A₁ A₂ B : SemTy}
    (r₁ : SemTy.eval n (.ref A₁) w) (r₂ : SemTy.eval n (.ref A₂) w)
    (k : SemTy.eval n (.arr A₁ (.arr A₂ (M B))) w) :
    M.bind (M.get r₁) (fun m₁ hm₁ w₁ hw₁ x =>
      M.bind (M.get (SemTy.map hw₁ (SemTy.restrict hm₁ r₂))) (fun m₂ hm₂ w₂ hw₂ y =>
        k m₂ (Nat.le_trans hm₂ hm₁) w₂ (World.step_le_trans hm₂ hm₁ hw₁ hw₂)
          (SemTy.map hw₂ (SemTy.restrict hm₂ x))
          m₂ (Nat.le_refl m₂) w₂ (by simpa using World.le_refl w₂) y)) =
    M.bind (M.get r₂) (fun m₁ hm₁ w₁ hw₁ y =>
      M.bind (M.get (SemTy.map hw₁ (SemTy.restrict hm₁ r₁))) (fun m₂ hm₂ w₂ hw₂ x =>
        k m₂ (Nat.le_trans hm₂ hm₁) w₂ (World.step_le_trans hm₂ hm₁ hw₁ hw₂)
          x m₂ (Nat.le_refl m₂) w₂ (by simpa using World.le_refl w₂)
          (SemTy.map hw₂ (SemTy.restrict hm₂ y)))) := by
  rcases r₁ with ⟨⟨l₁, hl₁⟩⟩
  rcases r₂ with ⟨⟨l₂, hl₂⟩⟩
  funext m hm w' hw' h
  cases m with
  | zero =>
    simp [M.bind, M.get]
  | succ m₀ =>
    cases m₀ with
    | zero =>
      simp [M.bind, M.get, SemTy.map, SemTy.restrict]
    | succ q =>
      cases n with
      | zero => omega
      | succ n₀ =>
        have hl₁' : w'.cells l₁ = some A₁ :=
          hw' l₁ A₁ (by simp [World.restrict_cells, hl₁, SemTy.nextAt, LaterTy.restrict])
        have hl₂' : w'.cells l₂ = some A₂ :=
          hw' l₂ A₂ (by simp [World.restrict_cells, hl₂, SemTy.nextAt, LaterTy.restrict])
        have hl₁_tr : w'.trunc.cells l₁ = some A₁ := by
          simp [World.trunc, World.restrict_cells, hl₁', LaterTy.restrict]
        have hl₂_tr : w'.trunc.cells l₂ = some A₂ := by
          simp [World.trunc, World.restrict_cells, hl₂', LaterTy.restrict]
        simp only [M.bind, M.get, SemTy.map, SemTy.restrict,
          StepLift.bind_stepSucc, StepLift.bind_ret, StepLift.map_stepSucc, StepLift.map_map]
        congr 2
        have hx_eq :
            SemTy.map (World.le_refl w'.trunc.trunc)
              (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl q))
                (CellVal.toEval (h.get l₁ A₁ hl₁'))) =
            CellVal.toEval ((TotHeap.trunc h).get l₁ A₁ hl₁_tr) := by
          rw [SemTy.map_refl, TotHeap.toEval_trunc_get h l₁ hl₁' hl₁_tr]
        have hy_eq :
            CellVal.toEval ((TotHeap.trunc h).get l₂ A₂ hl₂_tr) =
            SemTy.map (World.le_refl w'.trunc.trunc)
              (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl q))
                (CellVal.toEval (h.get l₂ A₂ hl₂'))) := by
          rw [SemTy.map_refl, TotHeap.toEval_trunc_get h l₂ hl₂' hl₂_tr]
        rw [hx_eq, hy_eq]

/-- **`set_after_get_unit` (`paper.tex:326`)**:
`x ← get r; set r x = step` (reading a cell and writing the identical value back
is observationally equal to a pure 1-step tick `step`!). -/
theorem set_after_get_unit {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) :
    M.bind (M.get r) (fun _ hm _ hw' x =>
      M.set (SemTy.map hw' (SemTy.restrict hm r)) x) = M.step := by
  rcases r with ⟨⟨l, hl⟩⟩
  funext m hm w' hw' h
  cases m with
  | zero =>
    simp [M.bind, M.get, M.step]
  | succ k =>
    cases n with
    | zero => omega
    | succ n₀ =>
      have hl' : w'.cells l = some A :=
        hw' l A (by simp [World.restrict_cells, hl, SemTy.nextAt, LaterTy.restrict])
      simp only [M.bind, M.get, M.set, M.step, SemTy.map, SemTy.restrict,
        StepLift.bind_stepSucc, StepLift.bind_ret, StepLift.map_ret,
        SemTy.restrict_refl_map]
      congr 2
      dsimp only [M.reanchorAns]
      have hl_tr : w'.trunc.cells l = some (SemTy.nextAt k A) := by
        cases k <;> simp [World.trunc, World.restrict_cells, SemTy.nextAt, LaterTy.restrict, hl']
      have hh_eq :
          TotHeap.update (A := A) (TotHeap.trunc h) l hl_tr
            (CellVal.nextVal (CellVal.toEval (h.get l A hl'))) =
          TotHeap.trunc h := by
        rw [TotHeap.nextVal_toEval_eq_trunc_get h l hl' hl_tr, TotHeap.update_self]
      congr 2
      exact Prod.ext hh_eq rfl

/-- **`set_after_get` (`paper.tex:326`, continuation form)**:
`(x ← get r; set r x ;; k x) = (x ← get r; k x)`. -/
theorem set_after_get {n : Nat} {w : World n} {A B : SemTy}
    (r : SemTy.eval n (.ref A) w) (k : SemTy.eval n (.arr A (M B)) w) :
    M.bind (M.get r) (fun m hm w' hw' x =>
      M.seq (M.set (SemTy.map hw' (SemTy.restrict hm r)) x)
        (k m hm w' hw' x)) =
    M.bind (M.get r) k := by
  rcases r with ⟨⟨l, hl⟩⟩
  funext m hm w' hw' h
  cases m with
  | zero =>
    simp [M.bind, M.get]
  | succ q =>
    cases n with
    | zero => omega
    | succ n₀ =>
      have hl' : w'.cells l = some A :=
        hw' l A (by simp [World.restrict_cells, hl, SemTy.nextAt, LaterTy.restrict])
      have hl_tr : w'.trunc.cells l = some (SemTy.nextAt q A) := by
        cases q <;> simp [World.trunc, World.restrict_cells, SemTy.nextAt, LaterTy.restrict, hl']
      simp only [M.bind, M.seq, M.get, M.set, SemTy.map, SemTy.restrict,
        StepLift.bind_stepSucc, StepLift.bind_ret, StepLift.map_map,
        SemTy.restrict_refl_map]
      have hh_eq :
          TotHeap.update (A := A) (TotHeap.trunc h) l hl_tr
            (CellVal.nextVal (CellVal.toEval (h.get l A hl'))) =
          TotHeap.trunc h := by
        rw [TotHeap.nextVal_toEval_eq_trunc_get h l hl' hl_tr, TotHeap.update_self]
      rw [hh_eq]
      dsimp only [M.reanchorAns]
      congr 2

/-! ## Positive Guarded Recursive Type Laws (`unfold_of_fold`, `fold_of_unfold`) -/

/-- `unfold (fold u) = step ;; ret u` (`paper.tex:339`). -/
theorem unfold_of_fold {n : Nat} {w : World n} {body : SemTy}
    (u : SemTy.eval n (body.subst0 (.mu body)) w) :
    M.unfold (SemTy.fold u) = M.seq M.step (M.ret u) := by
  funext m hm w' hw' h
  cases m with
  | zero =>
    simp [M.unfold, M.seq, M.bind, M.step]
  | succ k =>
    cases n with
    | zero => omega
    | succ q =>
      simp only [M.unfold, SemTy.fold, M.seq, M.bind, M.step, M.ret,
        SemTy.eval_comp_map_restrict, StepLift.bind_stepSucc, StepLift.bind_ret, StepLift.map_ret]
      congr 2
      dsimp only [M.reanchorAns]
      let hk_le : k ≤ k + 1 := Nat.le_succ_of_le (Nat.le_refl k)
      have hu_eq :
          CellVal.toEval (SemTy.map (A := .mu body) hw'
            (SemTy.restrict hm
              (CellVal.ofEval (w := w) (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl q)) u)))) =
          SemTy.map (World.step_le_trans hk_le hm hw' (World.le_refl w'.trunc))
            (SemTy.restrict (Nat.le_trans hk_le hm) u) := by
        simp only [SemTy.restrict, SemTy.map, CellVal.restrict, CellVal.map,
          CellVal.toEval_ofEval]
        rw [SemTy.map_trans,
          ← SemTy.restrict_trans_map (Nat.le_of_succ_le_succ hm)
            (Nat.le_succ_of_le (Nat.le_refl q))
            (World.restrict_trans_le _ _ w) u,
          SemTy.map_trans]
      congr 2
      exact Prod.ext rfl hu_eq

/-- `(x ← unfold u; ret (fold x)) = step ;; ret u` (`paper.tex:341`). -/
theorem fold_of_unfold {n : Nat} {w : World n} {body : SemTy}
    (u : SemTy.eval n (.mu body) w) :
    M.bind (M.unfold u) (fun _ _ _ _ x => M.ret (SemTy.fold x)) =
      M.seq M.step (M.ret u) := by
  funext m hm w' hw' h
  cases m with
  | zero =>
    simp [M.bind, M.unfold, M.seq, M.step]
  | succ k =>
    simp only [M.bind, M.unfold, M.seq, M.step, M.ret,
      SemTy.eval_comp_map_restrict, StepLift.bind_stepSucc, StepLift.bind_ret, StepLift.map_ret]
    congr 2
    dsimp only [M.reanchorAns]
    let hk_le : k ≤ k + 1 := Nat.le_succ_of_le (Nat.le_refl k)
    have hx_eq :
        SemTy.map (by simpa using World.le_refl w'.trunc)
          (SemTy.restrict (Nat.le_refl k)
            (SemTy.fold (CellVal.toEval (SemTy.map (A := .mu body) hw' (SemTy.restrict hm u))))) =
        SemTy.map (World.step_le_trans hk_le hm hw' (World.le_refl w'.trunc))
          (SemTy.restrict (Nat.le_trans hk_le hm) u) := by
      rw [SemTy.restrict_refl_map (World.restrict_refl_le w'.trunc)]
      have hrhs : SemTy.map (World.step_le_trans hk_le hm hw' (World.le_refl w'.trunc))
          (SemTy.restrict (Nat.le_trans hk_le hm) u) =
          SemTy.restrict hk_le (SemTy.map hw' (SemTy.restrict hm u)) := by
        rw [SemTy.restrict_map_comm hk_le hw' (SemTy.restrict hm u),
          ← SemTy.restrict_trans_map hk_le hm (World.restrict_trans_le hk_le hm w) u,
          SemTy.map_trans]
      rw [hrhs]
      let u' : SemTy.eval (k + 1) (.mu body) w' := SemTy.map hw' (SemTy.restrict hm u)
      change SemTy.fold (CellVal.toEval u') = SemTy.restrict hk_le u'
      cases k with
      | zero => rfl
      | succ q =>
        simp only [SemTy.fold, SemTy.restrict, CellVal.restrict]
        have htr_refl : World.trunc_restrict_le (Nat.le_succ_of_le (Nat.le_refl (q + 1))) w' =
            World.le_refl w'.trunc.trunc := rfl
        rw [htr_refl, SemTy.map_refl]
    congr 2
    exact Prod.ext rfl hx_eq

/-! ## Negative Tightness Counterexamples (`≠`) -/

/-- Canonical 1-cell stage-1 world `{1 : ref Nat}` and total heap `{1 ↦ 0}` for
tightness counterexamples. -/
noncomputable def eqTestWorld : World 1 :=
  (World.empty 1).insert 1 SemTy.nat

noncomputable def eqTestRef : SemTy.eval 1 (.ref SemTy.nat) eqTestWorld :=
  ⟨⟨1, by simp [eqTestWorld, SemTy.nextAt]⟩⟩

noncomputable def eqTestHeap : TotHeap 1 eqTestWorld :=
  TotHeap.alloc (Heaplet.empty (World.empty 1)) (A := SemTy.nat) (CellVal.nextVal (ULift.up 0))

/-- **Tightness Counterexample 1 (`not_get_after_set_nostep`)**:
`set r v ;; get r ≠ set r v ;; ret v` because `get r` incurs 1 guarded step (`Sum.inr`),
whereas `set r v ;; ret v` terminates in 0 steps (`Sum.inl`)! -/
theorem not_get_after_set_nostep :
    M.seq (M.set (A := SemTy.nat) eqTestRef (ULift.up 42)) (M.get eqTestRef) ≠
      M.seq (M.set (A := SemTy.nat) eqTestRef (ULift.up 42))
        (M.ret (A := SemTy.nat) (ULift.up 42)) := by
  intro heq
  have hval := congrFun (congrFun (congrFun (congrFun (congrFun heq 1) (Nat.le_refl 1))
    eqTestWorld) (by simpa using World.le_refl eqTestWorld)) eqTestHeap
  simp only [M.seq, M.bind, M.set, M.get, M.ret, SemTy.eval_comp_map_restrict,
    StepLift.bind_ret, StepLift.map_stepSucc, StepLift.map_ret] at hval
  simp [StepLift.ret, StepLift.stepSucc] at hval

/-- **Tightness Counterexample 2 (`not_diagonal_get_idempotent`)**:
`(x ← get r; y ← get r; ret (x, y)) ≠ (x ← get r; ret (x, x))` because reading `r`
twice takes **2** guarded steps (`Sum.inr (Sum.inr ())` at stage `1`) vs. **1** step
(`Sum.inr (Sum.inl _)` at stage `1`)! -/
theorem not_diagonal_get_idempotent :
    M.bind (M.get eqTestRef) (fun _ hm₁ _ hw₁ x =>
      M.bind (M.get (SemTy.map hw₁ (SemTy.restrict hm₁ eqTestRef))) (fun _ hm₂ _ hw₂ y =>
        M.ret (A := .prod SemTy.nat SemTy.nat)
          (SemTy.map hw₂ (SemTy.restrict hm₂ x), y))) ≠
    M.bind (M.get eqTestRef) (fun _ _ _ _ x =>
      M.ret (A := .prod SemTy.nat SemTy.nat) (x, x)) := by
  intro heq
  have hval := congrFun (congrFun (congrFun (congrFun (congrFun heq 1) (Nat.le_refl 1))
    eqTestWorld) (by simpa using World.le_refl eqTestWorld)) eqTestHeap
  simp only [M.bind, M.get, M.ret, SemTy.map, SemTy.restrict,
    StepLift.bind_stepSucc, StepLift.bind_ret, StepLift.map_ret] at hval
  dsimp only [StepLift.stepSucc, StepLift.stepZero, StepLift.ret, StepLift.map] at hval
  injection hval with hval
  nomatch hval

/-- **Tightness Counterexample 3 (`not_dead_new_elim`)**:
`(new 0 ;; ret ()) ≠ ret ()` in TULIP's global-store semantics (`paper.tex:308`),
because unused allocation strictly grows the returned world (`w'.cells 1 = some Nat` vs `none`)! -/
theorem not_dead_new_elim :
    M.seq (M.new (n := 1) (w := World.empty 1) (A := SemTy.nat) (ULift.up 0))
      (M.ret (A := SemTy.unit) (ULift.up PUnit.unit)) ≠
    M.ret (n := 1) (w := World.empty 1) (A := SemTy.unit) (ULift.up PUnit.unit) := by
  intro heq
  have hval := congrFun (congrFun (congrFun (congrFun (congrFun heq 1) (Nat.le_refl 1))
    (World.empty 1)) (by simpa using World.le_refl (World.empty 1)))
    (Heaplet.empty (World.empty 1))
  simp only [M.seq, M.bind, M.new, M.ret, SemTy.eval_comp_map_restrict,
    StepLift.bind_ret, StepLift.map_ret, M.reanchorAns] at hval
  dsimp only [StepLift.ret] at hval
  injection hval with hval
  have hworld : ((World.empty 1).insert (World.empty 1).fresh SemTy.nat).cells 1 =
      (World.empty 1).cells 1 :=
    congrArg (fun ans => ans.1.cells 1) hval
  have hfresh : (World.empty 1).fresh = 1 := rfl
  rw [hfresh] at hworld
  simp at hworld

/-- **Tightness Counterexample 4 (`not_new_comm`)**:
`(r ← new 10; s ← new 20; ret (r, s)) ≠ (s ← new 20; r ← new 10; ret (r, s))`
because deterministic `fresh w' = maxLoc w' + 1` assigns location `1` to the first
allocation and location `2` to the second (`(1, 2) ≠ (2, 1)`)! -/
theorem not_new_comm :
    M.bind (M.new (n := 1) (w := World.empty 1) (A := SemTy.nat) (ULift.up 10))
      (fun m₁ _ w₁ _ r =>
        M.bind (M.new (n := m₁) (w := w₁) (A := SemTy.nat) (ULift.up 20))
          (fun _ hm₂ _ hw₂ s =>
            M.ret (A := .prod (.ref SemTy.nat) (.ref SemTy.nat))
              (SemTy.map hw₂ (SemTy.restrict hm₂ r), s))) ≠
    M.bind (M.new (n := 1) (w := World.empty 1) (A := SemTy.nat) (ULift.up 20))
      (fun m₁ _ w₁ _ s =>
        M.bind (M.new (n := m₁) (w := w₁) (A := SemTy.nat) (ULift.up 10))
          (fun _ hm₂ _ hw₂ r =>
            M.ret (A := .prod (.ref SemTy.nat) (.ref SemTy.nat))
              (r, SemTy.map hw₂ (SemTy.restrict hm₂ s)))) := by
  intro heq
  have hval := congrFun (congrFun (congrFun (congrFun (congrFun heq 1) (Nat.le_refl 1))
    (World.empty 1)) (by simpa using World.le_refl (World.empty 1)))
    (Heaplet.empty (World.empty 1))
  simp only [M.bind, M.new, M.ret, SemTy.map, SemTy.restrict,
    StepLift.bind_ret, StepLift.map_ret, M.reanchorAns] at hval
  dsimp only [StepLift.ret] at hval
  injection hval with hval
  have hfst_loc : (World.empty 1).fresh =
      ((World.empty 1).insert (World.empty 1).fresh (SemTy.nextAt 1 SemTy.nat)).fresh :=
    congrArg (fun ans => ans.2.2.2.1.down.1) hval
  dsimp only [SemTy.nextAt] at hfst_loc
  have hf1 : (World.empty 1).fresh = 1 := rfl
  rw [hf1] at hfst_loc
  let w₁ := (World.empty 1).insert 1 SemTy.nat
  have hnone : w₁.cells w₁.fresh = none := w₁.cells_fresh
  rw [← hfst_loc] at hnone
  simp [w₁] at hnone

/-! ## Partial-Correctness Divergence Witness (`diverge_wp_false`) -/

theorem M.diverge_go_lLift {A : SemTy} :
    ∀ (m : Nat) (w' : World m) (Φ : ∀ (j : Nat) (hj : j ≤ m), CompAns A m w' j hj → Prop),
      StepLift.lLift (M.diverge.go m w') Φ
  | 0,     _,  _ => trivial
  | k + 1, w', _ => by
      simp only [M.diverge.go, StepLift.lLift_stepSucc, StepLift.lLift_map]
      exact M.diverge_go_lLift k w'.trunc _

/-- **`diverge_wp_false` (Partial-only correctness witness)**:
The diverging computation `M.diverge : M A` (`Ω = gfix step`) satisfies
`⊤ ⊢ wpRepaired M.diverge (fun _ => ⊥)` at all stages `n` and worlds `w`! -/
theorem diverge_wp_false (n : Nat) (w : World n) (A : SemTy) :
    BIProp.Entails (BIProp.top n w)
      (wpRepaired (M.diverge (n := n) (A := A) (w := w))
        (BIPred.const A (BIProp.bot n w))) := by
  intro _ _ _ _ _ _ m' _ w' _ _ _ _ _
  exact M.diverge_go_lLift m' w' _

end Tulip
