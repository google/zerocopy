-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import TulipModel.Logic

/-!
# Published `Swp` World-Variance Bug vs. Repaired `Swp` Soundness

1. Encodes TULIP's literal published `Swp` (`wpPublishedAt`, `paper.tex:1844–1868`),
   where the returned local heap `h'` must inhabit `TotHeap j w'' = Heaplet j w'' w''`
   rather than `ParHeap j w_r` (`Heaplet j w'' w_r`).
2. Proves concrete negative counterexamples showing that when a locally owned cell
   `l_local : ref (ref Nat)` stores a reference `l_frame : ref Nat` owned by the
   frame `h_f`:
   - `published_wp_set_frame_ref_unsound`: the antecedent of `wp-set` holds, yet
     `wpPublishedAt` of `set l_local l_frame` is `False`!
   - `published_wp_get_frame_ref_unsound`: the antecedent of `wp-get` holds, yet
     `wpPublishedAt` of `get l_local` is `False`!
   - `published_wp_not_heap_monotone`: `wpPublishedAt` of `ret ()` even violates
     `ParHeap` extension monotonicity (`∅ ≤ h`), so the published `Swp` is not even
     well-typed as an element of `ℬ = [pH, Prop_𝕎]`!
3. Encodes `wpRepaired` (`h' : ParHeap j w_r` with `h'.suppWorld = w''`) as a genuine
   `BIProp n w` and proves full soundness (`wp_val`, `wp_wand`, `wp_frame`, `wp_bind`,
   `wp_step`, `wp_get`, `wp_set`, `wp_new`, `wp_rec`) plus the positive verification
   of the exact frame-reference `set`/`get` programs!
-/

namespace Tulip

/-! ## Part 1: Total-to-Partial Heap Decomposition Helpers -/

@[simp]
theorem SemTy.map_ref_val {n : Nat} {A : SemTy} {w₁ w₂ : World n}
    (hle : World.Le w₁ w₂) (r : SemTy.eval n (.ref A) w₁) :
    (SemTy.map (A := .ref A) hle r).down.1 = r.down.1 := by
  rcases r with ⟨⟨_, _⟩⟩; simp [SemTy.map]

@[simp]
theorem SemTy.restrict_ref_val {m n : Nat} (hmn : m ≤ n) {A : SemTy} {w : World n}
    (r : SemTy.eval n (.ref A) w) :
    (SemTy.restrict (A := .ref A) hmn r).down.1 = r.down.1 := by
  rcases r with ⟨⟨_, _⟩⟩; simp [SemTy.restrict]

theorem ParHeap.eta_get_of_eq {n : Nat} {w : World n} {p₁ p₂ : ParHeap n w}
    (heq : p₁ = p₂) (l : Loc) (T : LaterTy n)
    (hc₁ : (w.restrictDom p₁.dom).cells l = some T)
    (hc₂ : (w.restrictDom p₂.dom).cells l = some T) :
    p₁.eta.get l T hc₁ = p₂.eta.get l T hc₂ := by
  subst heq
  rfl

theorem TotHeap.world_eq_of_toParHeap_union {n : Nat} {w : World n}
    {h_t : TotHeap n w} {h₁ h₂ : ParHeap n w}
    (hd : ParHeap.Disjoint h₁ h₂)
    (htot : h_t.toParHeap = h₁.union h₂) :
    w = h₂.suppWorld.union h₁.suppWorld := by
  have hsupp := congrArg ParHeap.suppWorld htot
  rw [TotHeap.toParHeap_suppWorld, ParHeap.suppWorld_union,
    World.union_comm hd.worldDisjoint] at hsupp
  exact hsupp

theorem TotHeap.trunc_toParHeap {k : Nat} {w : World (k + 1)} (h_t : TotHeap (k + 1) w) :
    (TotHeap.trunc h_t).toParHeap =
      h_t.toParHeap.restrict (Nat.le_succ_of_le (Nat.le_refl k)) := by
  refine ParHeap.ext ?_ ?_
  · intro l
    simp only [TotHeap.toParHeap, ParHeap.restrict_dom, World.trunc, World.restrict_cells]
    cases w.cells l <;> rfl
  · intro l T _ _
    cases k with
    | zero => rfl
    | succ _ =>
      simp [TotHeap.toParHeap, ParHeap.restrict, Heaplet.restrict]

theorem TotHeap.update_toParHeap_split {n : Nat} {w : World n} {A : SemTy}
    (h_t : TotHeap n w) (h_f h_rest : ParHeap n w)
    (l : Loc) (hl : w.cells l = some (SemTy.nextAt n A))
    (y a : SemTy.eval n A w)
    (hd_single_rest : ParHeap.Disjoint (ParHeap.singleton l hl y) h_rest)
    (hd_f_loc : ParHeap.Disjoint h_f ((ParHeap.singleton l hl y).union h_rest))
    (htot : h_t.toParHeap = h_f.union ((ParHeap.singleton l hl y).union h_rest)) :
    (h_t.update l hl (CellVal.nextVal a)).toParHeap =
      h_f.union ((ParHeap.singleton l hl a).union h_rest) := by
  have hd_f_l : h_f.dom l = false := by
    rcases hd_f_loc l with df | dloc
    · exact df
    · simp only [ParHeap.union_dom, ParHeap.singleton_dom, beq_self_eq_true, Bool.true_or] at dloc
      contradiction
  have hdom_eq : ∀ l', (h_t.update l hl (CellVal.nextVal a)).toParHeap.dom l' =
      (h_f.union ((ParHeap.singleton l hl a).union h_rest)).dom l' := by
    intro l'
    have hdom_orig := congrArg (fun p => p.dom l') htot
    simpa [TotHeap.toParHeap, ParHeap.union_dom, ParHeap.singleton_dom] using hdom_orig
  refine ParHeap.ext hdom_eq ?_
  intro l' T _ hw'
  by_cases heq : l' = l
  · subst heq
    have hT : SemTy.nextAt n A = T := Option.some.inj (hl.symm.trans hw')
    subst hT
    simp [TotHeap.toParHeap, TotHeap.update, ParHeap.union, ParHeap.singleton, hd_f_l]
  · have hbeq : (l' == l) = false := beq_false_of_ne heq
    have hd_true : (h_f.union ((ParHeap.singleton l hl y).union h_rest)).dom l' = true := by
      have hdom_orig := congrArg (fun p => p.dom l') htot
      dsimp only at hdom_orig
      rw [← hdom_orig]
      simp [TotHeap.toParHeap, hw']
    have hget_orig : h_t.get l' T hw' =
        (h_f.union ((ParHeap.singleton l hl y).union h_rest)).eta.get l' T
          (by rw [World.restrictDom_cells, hd_true]; exact hw') :=
      ParHeap.eta_get_of_eq htot l' T (by simp [TotHeap.toParHeap, hw']) _
    dsimp only [TotHeap.toParHeap]
    rw [TotHeap.update_other h_t l l' heq hl _ T hw', hget_orig]
    cases df : h_f.dom l'
    · simp [ParHeap.union, df, ParHeap.singleton_dom, heq]
    · simp [ParHeap.union, df]

theorem TotHeap.alloc_toParHeap_split {n : Nat} {w : World n} {A : SemTy}
    (h_t : TotHeap n w) (h_f h_loc : ParHeap n w)
    (htot : h_t.toParHeap = h_f.union h_loc)
    (a : SemTy.eval n A (w.insert w.fresh (SemTy.nextAt n A))) :
    let T_n := SemTy.nextAt n A
    let w'' := w.insert w.fresh T_n
    let hle : World.Le w w'' := World.le_insert_fresh w T_n
    let hl_fresh : w''.cells w.fresh = some T_n := by simp [w'']
    (h_t.alloc (CellVal.nextVal a)).toParHeap =
      (h_f.map hle).union ((h_loc.map hle).union (ParHeap.singleton w.fresh hl_fresh a)) := by
  intro T_n w'' hle hl_fresh
  have hf_fresh : h_f.dom w.fresh = false := by
    cases hd : h_f.dom w.fresh
    · rfl
    · have hs := h_f.dom_sub w.fresh hd
      rw [w.cells_fresh] at hs
      contradiction
  have hloc_fresh : h_loc.dom w.fresh = false := by
    cases hd : h_loc.dom w.fresh
    · rfl
    · have hs := h_loc.dom_sub w.fresh hd
      rw [w.cells_fresh] at hs
      contradiction
  have hdom_eq : ∀ l, (h_t.alloc (CellVal.nextVal a)).toParHeap.dom l =
      ((h_f.map hle).union ((h_loc.map hle).union (ParHeap.singleton w.fresh hl_fresh a))).dom l := by
    intro l
    by_cases heq : l = w.fresh
    · subst heq
      simp [TotHeap.toParHeap, w'', hf_fresh, hloc_fresh]
    · have hbeq : (l == w.fresh) = false := beq_false_of_ne heq
      have hdom_orig := congrArg (fun p => p.dom l) htot
      dsimp only [TotHeap.toParHeap, ParHeap.union_dom] at hdom_orig
      simp [TotHeap.toParHeap, w'', hbeq, hdom_orig]
  refine ParHeap.ext hdom_eq ?_
  intro l T _ hw''
  by_cases heq : l = w.fresh
  · subst heq
    have hT : T_n = T := Option.some.inj (hl_fresh.symm.trans hw'')
    subst hT
    simp [TotHeap.toParHeap, TotHeap.alloc, ParHeap.union, ParHeap.singleton,
      hf_fresh, hloc_fresh]
  · have hbeq : (l == w.fresh) = false := beq_false_of_ne heq
    have hw_l : w.cells l = some T := by
      simpa [w'', World.insert_cells, hbeq] using hw''
    have hd_true : (h_f.union h_loc).dom l = true := by
      have hdom_orig := congrArg (fun p => p.dom l) htot
      dsimp only at hdom_orig
      rw [← hdom_orig]
      simp [TotHeap.toParHeap, hw_l]
    have hget_orig : h_t.get l T hw_l =
        (h_f.union h_loc).eta.get l T (by rw [World.restrictDom_cells, hd_true]; exact hw_l) :=
      ParHeap.eta_get_of_eq htot l T (by simp [TotHeap.toParHeap, hw_l]) _
    dsimp only [TotHeap.toParHeap]
    simp only [TotHeap.alloc, heq, ↓reduceDIte]
    rw [show h_t.get l T _ = h_t.get l T hw_l from rfl, hget_orig]
    cases df : h_f.dom l
    · have dloc : h_loc.dom l = true := by
        simp only [ParHeap.union_dom, df, Bool.false_or] at hd_true
        exact hd_true
      simp [ParHeap.union, ParHeap.map, df, dloc]
    · simp [ParHeap.union, ParHeap.map, df]

/-! ## Part 2: Published `Swp` (`paper.tex:1844–1868`) and World-Variance Bug Counterexamples -/

/-- Literal Kripke–Joyal forcing clause of TULIP's published `Swp_A` (`paper.tex:1838–1868`):
`w ⊩ (h ⊩ Swp_A u Φ)` at stage `n`, world `w`, and partial heap `h : ParHeap n w`.
Note line 1855: `h' : TotalHeap_{w''}` (`TotHeap j w''`), forcing all cell values inside
`h'` to evaluate at world `w''` (excluding `|h_f|`) rather than at `w_r = w'' · |h_f|`! -/
def wpPublishedAt {n : Nat} {w : World n} {A : SemTy}
    (u : SemTy.eval n (M A) w) (Φ : BIPred n w A) (h : ParHeap n w) : Prop :=
  ∀ (w' : World n) (hw' : World.Le w w')
    (h_f : ParHeap n w') (_ : ParHeap.Disjoint h_f (h.map hw'))
    (h_t : TotHeap n w'),
    h_t.toParHeap = h_f.union (h.map hw') →
    StepLift.lLift
      (u n (Nat.le_refl n) w' (World.le_trans (World.restrict_refl_le w) hw') h_t)
      (fun j hj ans =>
        ∃ (w'' : World j)
          (_ : World.Le ((h.map hw').restrict hj).suppWorld w'')
          (_ : World.Disjoint w'' (h_f.restrict hj).suppWorld)
          (hw_r_eq : ans.1 = w''.union (h_f.restrict hj).suppWorld)
          (h' : TotHeap j w''),
          let hw''_le : World.Le w'' ans.1 := by
            rw [hw_r_eq]; exact World.le_union_left w'' (h_f.restrict hj).suppWorld
          TotHeap.toParHeap ans.2.2.1 =
              ((h_f.restrict hj).map ans.2.1.proof).union
                ((TotHeap.toParHeap h').map hw''_le) ∧
          Φ.holds j hj ans.1
            (World.step_le_trans hj (Nat.le_refl n)
              (World.le_trans (World.restrict_refl_le w) hw') ans.2.1.proof)
            ans.2.2.2 ((TotHeap.toParHeap h').map hw''_le))

section Counterexample

/-- Frame location `lFrame = 0` (`ref Nat`) and local location `lLocal = 1` (`ref (ref Nat)`). -/
abbrev lFrame : Loc := 0
abbrev lLocal : Loc := 1

/-- Two-cell world `w = { 0 : ref Nat, 1 : ref (ref Nat) }` at stage `k + 1`. -/
noncomputable def bugWorld (k : Nat) : World (k + 1) :=
  (World.singleton (k + 1) lFrame SemTy.nat).insert lLocal (.ref SemTy.nat)

theorem bugWorld_frame_cell (k : Nat) :
    (bugWorld k).cells lFrame = some SemTy.nat := by
  simp [bugWorld, lFrame, lLocal]

theorem bugWorld_local_cell (k : Nat) :
    (bugWorld k).cells lLocal = some (.ref SemTy.nat) := by
  simp [bugWorld, lFrame, lLocal]

/-- Semantic reference `rFrame : ref Nat` at `bugWorld k`. -/
noncomputable def rFrame (k : Nat) : SemTy.eval (k + 1) (.ref SemTy.nat) (bugWorld k) :=
  ⟨⟨lFrame, bugWorld_frame_cell k⟩⟩

/-- Semantic nested reference `rLocal : ref (ref Nat)` at `bugWorld k`. -/
noncomputable def rLocal (k : Nat) : SemTy.eval (k + 1) (.ref (.ref SemTy.nat)) (bugWorld k) :=
  ⟨⟨lLocal, bugWorld_local_cell k⟩⟩

/-- Local partial heap owning ONLY `{lLocal}` and storing `rFrame` (`{1 ↦ next 0}`). -/
noncomputable def bugLocalHeap (k : Nat) : ParHeap (k + 1) (bugWorld k) :=
  ParHeap.singleton lLocal (bugWorld_local_cell k) (rFrame k)

/-- Frame partial heap owning ONLY `{lFrame}` and storing `42` (`{0 ↦ next 42}`). -/
noncomputable def bugFrameHeap (k : Nat) : ParHeap (k + 1) (bugWorld k) :=
  ParHeap.singleton (A := SemTy.nat) lFrame (bugWorld_frame_cell k) ⟨42⟩

theorem bugHeaps_disjoint (k : Nat) :
    ParHeap.Disjoint (bugFrameHeap k) (bugLocalHeap k) := by
  intro l
  by_cases h0 : l = lFrame
  · subst h0; right; rfl
  · left; exact beq_false_of_ne h0

theorem bugHeaps_suppWorld (k : Nat) :
    ((bugFrameHeap k).union (bugLocalHeap k)).suppWorld = bugWorld k := by
  apply World.ext
  intro l
  simp only [ParHeap.suppWorld, World.restrictDom_cells, ParHeap.union_dom,
    bugFrameHeap, bugLocalHeap, ParHeap.singleton_dom, bugWorld,
    World.insert_cells, World.singleton_cells]
  by_cases h1 : l = lLocal
  · subst h1; rfl
  · have hb1 : (l == lLocal) = false := beq_false_of_ne h1
    by_cases h0 : l = lFrame
    · subst h0; rfl
    · have hb0 : (l == lFrame) = false := beq_false_of_ne h0
      simp [hb1, hb0]

/-- Key impossibility lemma: at stage `k + 1`, no `h' : TotHeap (k + 1) w''` over a world `w''`
disjoint from `{lFrame}` can agree with `{lLocal ↦ next rFrame}` at `lLocal`! -/
theorem no_published_totHeap_with_frame_ref {k : Nat}
    {w'' : World (k + 1)}
    (hw''_local : w''.cells lLocal = some (.ref SemTy.nat))
    (hw''_no_frame : w''.cells lFrame = none)
    (hw''_le : World.Le w'' (bugWorld k))
    (h' : TotHeap (k + 1) w'')
    (heq_total : ((bugFrameHeap k).union (bugLocalHeap k)) =
      (bugFrameHeap k).union (h'.toParHeap.map hw''_le)) :
    False := by
  have hcell_lhs : ((bugFrameHeap k).union (bugLocalHeap k)).eta.get
      lLocal (.ref SemTy.nat) (by simp [bugLocalHeap, bugWorld_local_cell]) =
      CellVal.nextVal (rFrame k) := by
    simp [bugFrameHeap, bugLocalHeap, ParHeap.union, ParHeap.singleton, lLocal, lFrame]
  have hw''_dom : (h'.toParHeap.map hw''_le).dom lLocal = true := by
    simp [TotHeap.toParHeap, hw''_local]
  have hcell_rhs : ((bugFrameHeap k).union (h'.toParHeap.map hw''_le)).eta.get
      lLocal (.ref SemTy.nat) (by simp [TotHeap.toParHeap, hw''_local, bugWorld_local_cell]) =
      CellVal.map (k + 1) (.ref SemTy.nat) hw''_le
        (h'.get lLocal (.ref SemTy.nat) hw''_local) := by
    simp [bugFrameHeap, ParHeap.union, ParHeap.map, TotHeap.toParHeap, lLocal, lFrame]
  have heq_val : CellVal.nextVal (rFrame k) =
      CellVal.map (k + 1) (.ref SemTy.nat) hw''_le
        (h'.get lLocal (.ref SemTy.nat) hw''_local) := by
    rw [← hcell_lhs, ← hcell_rhs]
    exact ParHeap.eta_get_of_eq heq_total lLocal (.ref SemTy.nat) _ _
  have heq_eval := congrArg CellVal.toEval heq_val
  simp only [CellVal.nextVal, CellVal.map, CellVal.toEval_ofEval] at heq_eval
  let ref_in_w'' : SemTy.eval k (.ref SemTy.nat) w''.trunc :=
    CellVal.toEval (h'.get lLocal (.ref SemTy.nat) hw''_local)
  have hloc_eq : lFrame = ref_in_w''.down.1 := by
    have := congrArg (fun (r : SemTy.eval k (.ref SemTy.nat) (bugWorld k).trunc) => r.down.1)
      heq_eval
    simpa [rFrame, ref_in_w'', SemTy.restrict, SemTy.map] using this
  have h_in_w'' : (w''.trunc).cells ref_in_w''.down.1 = some (SemTy.nextAt k SemTy.nat) :=
    ref_in_w''.down.2
  rw [← hloc_eq, World.restrict_cells, hw''_no_frame] at h_in_w''
  contradiction

/-- General predicate `(∃ y, [r ↦ y])` for any reference `r : ref A` (reused in `wp_set`). -/
noncomputable def pointsToAnyPred {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) : BIPred n w A where
  holds m hm w' hw' y h' :=
    have hl' : w'.cells r.down.1 = some (SemTy.nextAt m A) :=
      hw' r.down.1 (SemTy.nextAt m A) (by simp [World.restrict_cells, r.down.2])
    ParHeap.Le (ParHeap.singleton r.down.1 hl' y) h'
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 y h₁ h₂ hh hp
    dsimp only at hp ⊢
    have hmon := ParHeap.map_mono hw12 (ParHeap.restrict_mono hm12 hp)
    rw [ParHeap.restrict_singleton, ParHeap.map_singleton] at hmon
    exact ParHeap.le_trans hmon hh

/-- `∃ y, [r ↦ y]` in `BIProp n w`. -/
noncomputable def BIProp.pointsToSome {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) : BIProp n w :=
  BIProp.existsSem (pointsToAnyPred r)

/-- **Counterexample 1 (`wp-set` unsoundness of TULIP's published `Swp`)**:
At stage `1`, world `bugWorld 0 = {0 : ref Nat, 1 : ref (ref Nat)}`, and local partial
heap `bugLocalHeap 0 = {1 ↦ next 0}`:
1. The antecedent `(∃ y, [lLocal ↦ y]) ∗ ([lLocal ↦ rFrame] -∗ ⊤)` of `wp-set`
   (`paper.tex:758`) **holds** at `(1, bugWorld 0, bugLocalHeap 0)`, AND YET
2. `wpPublishedAt (M.set rLocal rFrame) ⊤ (bugLocalHeap 0)` is **`False`**! -/
theorem published_wp_set_frame_ref_unsound :
    ((BIProp.pointsToSome (rLocal 0)).sep
      ((BIProp.pointsTo (rLocal 0) (rFrame 0)).wand (BIProp.top 1 (bugWorld 0)))).holds
        1 (Nat.le_refl 1) (bugWorld 0) (World.restrict_refl_le (bugWorld 0)) (bugLocalHeap 0) ∧
    ¬ wpPublishedAt (M.set (rLocal 0) (rFrame 0))
        (BIPred.const SemTy.unit (BIProp.top 1 (bugWorld 0))) (bugLocalHeap 0) := by
  constructor
  · refine ⟨bugLocalHeap 0, ParHeap.empty 1 (bugWorld 0),
      ParHeap.disjoint_empty_right _, (ParHeap.union_empty _).symm, ?_, ?_⟩
    · exact ⟨rFrame 0, ParHeap.le_refl _⟩
    · intro _ _ _ _ _ _ _
      trivial
  · intro hwp
    let h_f := bugFrameHeap 0
    let h   := bugLocalHeap 0
    have hd : ParHeap.Disjoint h_f (h.map (World.le_refl (bugWorld 0))) := by
      rw [ParHeap.map_refl]
      exact bugHeaps_disjoint 0
    let h_t : TotHeap 1 (bugWorld 0) := (h_f.union h).toTotHeap (bugHeaps_suppWorld 0)
    have htot : h_t.toParHeap = h_f.union (h.map (World.le_refl (bugWorld 0))) := by
      rw [ParHeap.map_refl]
      exact ParHeap.toTotHeap_toParHeap (h_f.union h) (bugHeaps_suppWorld 0)
    have hres := hwp (bugWorld 0) (World.le_refl (bugWorld 0)) h_f hd h_t htot
    simp only [M.set, StepLift.lLift_ret] at hres
    rcases hres with ⟨w'', hw''_ge, hw''_disj, hw_r_eq, h', heq_par, _⟩
    have hw''_local : w''.cells lLocal = some (.ref SemTy.nat) := by
      apply hw''_ge lLocal (.ref SemTy.nat)
      simp [bugLocalHeap, ParHeap.suppWorld, World.restrictDom_cells,
        lLocal, bugWorld_local_cell]
    have hw''_no_frame : w''.cells lFrame = none := by
      rcases hw''_disj lFrame with hnone | hf_none
      · exact hnone
      · exfalso
        simp [h_f, bugFrameHeap, ParHeap.suppWorld, World.restrictDom_cells,
          lFrame, bugWorld_frame_cell] at hf_none
    have h_upd_eq : ∀ (hl₀ : (bugWorld 0).cells lLocal = some (.ref SemTy.nat))
        (hle₀ : World.Le ((bugWorld 0).restrict (Nat.le_refl 1)) (bugWorld 0)),
        (TotHeap.update h_t lLocal hl₀
          (CellVal.nextVal (SemTy.map hle₀ (SemTy.restrict (Nat.le_refl 1) (rFrame 0))))).toParHeap =
          h_f.union h := by
      intro hl₀ hle₀
      have hr : SemTy.map hle₀ (SemTy.restrict (Nat.le_refl 1) (rFrame 0)) = rFrame 0 :=
        SemTy.restrict_refl_map hle₀ (rFrame 0)
      rw [hr]
      have hsplit := TotHeap.update_toParHeap_split h_t h_f (ParHeap.empty 1 (bugWorld 0))
        lLocal hl₀ (rFrame 0) (rFrame 0)
        (ParHeap.disjoint_empty_right _)
        (by rw [ParHeap.union_empty]; exact bugHeaps_disjoint 0)
        (by rw [ParHeap.union_empty]; exact ParHeap.toTotHeap_toParHeap _ (bugHeaps_suppWorld 0))
      rw [ParHeap.union_empty] at hsplit
      exact hsplit
    dsimp only [rLocal] at heq_par
    rw [h_upd_eq] at heq_par
    have hf_refl : (h_f.restrict (Nat.le_refl 1)).map
        (by simpa using World.le_refl (bugWorld 0)) = h_f := by
      simpa using ParHeap.restrict_refl_map h_f
    rw [hf_refl] at heq_par
    exact no_published_totHeap_with_frame_ref hw''_local hw''_no_frame
      (by rw [hw_r_eq]; exact World.le_union_left w'' _) h' heq_par

/-- **Counterexample 2 (`wp-get` unsoundness of TULIP's published `Swp`)**:
At stage `2`, world `bugWorld 1`, and local heap `bugLocalHeap 1`:
1. The antecedent `[lLocal ↦ rFrame] ∗ ▷ ([lLocal ↦ rFrame] -∗ ⊤)` of `wp-get`
   (`paper.tex:1998`) **holds** at `(2, bugWorld 1, bugLocalHeap 1)`, AND YET
2. `wpPublishedAt (M.get rLocal) ⊤ (bugLocalHeap 1)` is **`False`**! -/
theorem published_wp_get_frame_ref_unsound :
    ((BIProp.pointsTo (rLocal 1) (rFrame 1)).sep
      ((BIProp.pointsTo (rLocal 1) (rFrame 1)).wand (BIProp.top 2 (bugWorld 1))).later).holds
        2 (Nat.le_refl 2) (bugWorld 1) (World.restrict_refl_le (bugWorld 1)) (bugLocalHeap 1) ∧
    ¬ wpPublishedAt (M.get (rLocal 1))
        (BIPred.const (.ref SemTy.nat) (BIProp.top 2 (bugWorld 1))) (bugLocalHeap 1) := by
  constructor
  · refine ⟨bugLocalHeap 1, ParHeap.empty 2 (bugWorld 1),
      ParHeap.disjoint_empty_right _, (ParHeap.union_empty _).symm, ?_, ?_⟩
    · dsimp only [BIProp.pointsTo]
      have hr : SemTy.map (World.restrict_refl_le (bugWorld 1))
          (SemTy.restrict (Nat.le_refl 2) (rFrame 1)) = rFrame 1 :=
        SemTy.restrict_refl_map _ (rFrame 1)
      rw [hr]
      exact ParHeap.le_refl _
    · dsimp only [BIProp.later]
      intro _ _ _ _ _ _ _
      trivial
  · intro hwp
    let h_f := bugFrameHeap 1
    let h   := bugLocalHeap 1
    have hd : ParHeap.Disjoint h_f (h.map (World.le_refl (bugWorld 1))) := by
      rw [ParHeap.map_refl]
      exact bugHeaps_disjoint 1
    let h_t : TotHeap 2 (bugWorld 1) := (h_f.union h).toTotHeap (bugHeaps_suppWorld 1)
    have htot : h_t.toParHeap = h_f.union (h.map (World.le_refl (bugWorld 1))) := by
      rw [ParHeap.map_refl]
      exact ParHeap.toTotHeap_toParHeap (h_f.union h) (bugHeaps_suppWorld 1)
    have hres := hwp (bugWorld 1) (World.le_refl (bugWorld 1)) h_f hd h_t htot
    simp only [M.get, StepLift.lLift_stepSucc, StepLift.lLift_ret] at hres
    rcases hres with ⟨w'', hw''_ge, hw''_disj, hw_r_eq, h', heq_par, _⟩
    have hw_trunc_eq : (bugWorld 1).trunc = bugWorld 0 := by
      apply World.ext
      intro l
      simp only [World.trunc, World.restrict_cells, bugWorld,
        World.insert_cells, World.singleton_cells]
      by_cases h1 : l = lLocal
      · subst h1; rfl
      · have hb1 : (l == lLocal) = false := beq_false_of_ne h1
        by_cases h0 : l = lFrame
        · subst h0; rfl
        · have hb0 : (l == lFrame) = false := beq_false_of_ne h0
          simp [hb1, hb0]
    have hw''_local : w''.cells lLocal = some (.ref SemTy.nat) := by
      apply hw''_ge lLocal (.ref SemTy.nat)
      simp [bugLocalHeap, ParHeap.suppWorld, World.restrictDom_cells,
        lLocal, bugWorld_local_cell, LaterTy.restrict]
    have hw''_no_frame : w''.cells lFrame = none := by
      rcases hw''_disj lFrame with hnone | hf_none
      · exact hnone
      · exfalso
        simp [h_f, bugFrameHeap, ParHeap.suppWorld, World.restrictDom_cells,
          lFrame, bugWorld_frame_cell, LaterTy.restrict] at hf_none
    have hle_wb0 : World.Le (bugWorld 1).trunc (bugWorld 0) := by
      rw [hw_trunc_eq]; exact World.le_refl _
    have h_trunc_par : (TotHeap.trunc h_t).toParHeap.map hle_wb0 =
        (bugFrameHeap 0).union (bugLocalHeap 0) := by
      rw [TotHeap.trunc_toParHeap,
        show h_t.toParHeap = h_f.union h from
          ParHeap.toTotHeap_toParHeap (h_f.union h) (bugHeaps_suppWorld 1),
        ParHeap.restrict_union, ParHeap.map_union]
      congr 1
      · simp only [h_f, bugFrameHeap, ParHeap.restrict_singleton, ParHeap.map_singleton]
        refine ParHeap.ext (fun _ => rfl) ?_
        intro l' T hd' hw₀
        have heq_l : l' = lFrame := eq_of_beq hd'
        subst heq_l
        have hT : SemTy.nextAt 1 SemTy.nat = T :=
          Option.some.inj ((bugWorld_frame_cell 0).symm.trans hw₀)
        subst hT
        simp [ParHeap.singleton, CellVal.nextVal, SemTy.restrict, SemTy.map]
      · simp only [h, bugLocalHeap, ParHeap.restrict_singleton, ParHeap.map_singleton]
        refine ParHeap.ext (fun _ => rfl) ?_
        intro l' T hd' hw₀
        have heq_l : l' = lLocal := eq_of_beq hd'
        subst heq_l
        have hT : SemTy.nextAt 1 (.ref SemTy.nat) = T :=
          Option.some.inj ((bugWorld_local_cell 0).symm.trans hw₀)
        subst hT
        simp [ParHeap.singleton, CellVal.nextVal, SemTy.restrict, SemTy.map, rFrame]
    have heq_mapped := congrArg (ParHeap.map hle_wb0) heq_par
    rw [h_trunc_par, ParHeap.map_union, ParHeap.map_trans, ParHeap.map_trans] at heq_mapped
    have hf_0 : (h_f.restrict (Nat.le_succ_of_le (Nat.le_refl 1))).map
        (World.le_trans (World.le_refl (bugWorld 1).trunc) hle_wb0) = bugFrameHeap 0 := by
      simp only [h_f, bugFrameHeap, ParHeap.restrict_singleton, ParHeap.map_singleton]
      refine ParHeap.ext (fun _ => rfl) ?_
      intro l' T hd' hw₀
      have heq_l : l' = lFrame := eq_of_beq hd'
      subst heq_l
      have hT : SemTy.nextAt 1 SemTy.nat = T :=
        Option.some.inj ((bugWorld_frame_cell 0).symm.trans hw₀)
      subst hT
      simp [ParHeap.singleton, CellVal.nextVal, SemTy.restrict, SemTy.map]
    rw [hf_0] at heq_mapped
    exact no_published_totHeap_with_frame_ref hw''_local hw''_no_frame
      (World.le_trans (by rw [hw_r_eq]; exact World.le_union_left w'' _) hle_wb0)
      h' heq_mapped

/-- **Counterexample 3 (`wpPublishedAt` violates `ℬ = [pH, Prop_𝕎]` heap monotonicity & `wp-val`)**:
Even `M.ret ()` satisfies `wpPublishedAt` at `∅ : ParHeap 1 (bugWorld 0)`, yet **falsifies**
`wpPublishedAt` at `bugLocalHeap 0` despite `ParHeap.Le ∅ (bugLocalHeap 0)`! -/
theorem published_wp_not_heap_monotone :
    ParHeap.Le (ParHeap.empty 1 (bugWorld 0)) (bugLocalHeap 0) ∧
    wpPublishedAt (M.ret (A := SemTy.unit) ⟨PUnit.unit⟩)
      (BIPred.const SemTy.unit (BIProp.top 1 (bugWorld 0))) (ParHeap.empty 1 (bugWorld 0)) ∧
    ¬ wpPublishedAt (M.ret (A := SemTy.unit) ⟨PUnit.unit⟩)
      (BIPred.const SemTy.unit (BIProp.top 1 (bugWorld 0))) (bugLocalHeap 0) := by
  refine ⟨ParHeap.empty_le (bugLocalHeap 0), ?_, ?_⟩
  · intro w' hw' h_f _ h_t htot
    simp only [M.ret, StepLift.lLift_ret]
    have hemp_map : (ParHeap.empty 1 (bugWorld 0)).map hw' = ParHeap.empty 1 w' := by
      refine ParHeap.ext (fun _ => rfl) ?_
      intro _ _ hd' _; contradiction
    have h_f_supp : h_f.suppWorld = w' := by
      have hs := congrArg ParHeap.suppWorld htot
      rw [TotHeap.toParHeap_suppWorld, hemp_map, ParHeap.union_empty] at hs
      exact hs.symm
    refine ⟨World.empty 1, by simp [hemp_map]; exact World.le_refl _,
      fun _ => Or.inl rfl, ?_, Heaplet.empty (World.empty 1), ?_, trivial⟩
    · simp [ParHeap.suppWorld_restrict, World.restrict_refl, h_f_supp]
    · have hf_eq : (h_f.restrict (Nat.le_refl 1)).map (by simpa using World.le_refl w') = h_f := by
        simpa using ParHeap.restrict_refl_map h_f
      have h'_eq : (TotHeap.toParHeap (Heaplet.empty (World.empty 1))).map
          (World.empty_le w') = ParHeap.empty 1 w' := by
        refine ParHeap.ext (fun _ => rfl) ?_
        intro _ _ hd' _; simp [TotHeap.toParHeap] at hd'
      have h'_eq' : ∀ (hle_e : World.Le (World.empty 1) w'),
          (TotHeap.toParHeap (Heaplet.empty (World.empty 1))).map hle_e = ParHeap.empty 1 w' :=
        fun _ => h'_eq
      rw [hf_eq, h'_eq', ParHeap.union_empty, htot, hemp_map, ParHeap.union_empty]
  · intro hwp
    let h_f := bugFrameHeap 0
    let locH := bugLocalHeap 0
    have hd : ParHeap.Disjoint h_f (locH.map (World.le_refl (bugWorld 0))) := by
      rw [ParHeap.map_refl]; exact bugHeaps_disjoint 0
    let h_t : TotHeap 1 (bugWorld 0) := (h_f.union locH).toTotHeap (bugHeaps_suppWorld 0)
    have htot : h_t.toParHeap = h_f.union (locH.map (World.le_refl (bugWorld 0))) := by
      rw [ParHeap.map_refl]
      exact ParHeap.toTotHeap_toParHeap _ (bugHeaps_suppWorld 0)
    have hres := hwp (bugWorld 0) (World.le_refl (bugWorld 0)) h_f hd h_t htot
    simp only [M.ret, StepLift.lLift_ret] at hres
    rcases hres with ⟨w'', hw''_ge, hw''_disj, hw_r_eq, h', heq_par, _⟩
    have hw''_local : w''.cells lLocal = some (.ref SemTy.nat) := by
      apply hw''_ge lLocal (.ref SemTy.nat)
      simp [bugLocalHeap, ParHeap.suppWorld, World.restrictDom_cells,
        lLocal, bugWorld_local_cell]
    have hw''_no_frame : w''.cells lFrame = none := by
      rcases hw''_disj lFrame with hnone | hf_none
      · exact hnone
      · exfalso
        simp [h_f, bugFrameHeap, ParHeap.suppWorld, World.restrictDom_cells,
          lFrame, bugWorld_frame_cell] at hf_none
    rw [ParHeap.toTotHeap_toParHeap _ (bugHeaps_suppWorld 0)] at heq_par
    have hf_refl : (h_f.restrict (Nat.le_refl 1)).map
        (by simpa using World.le_refl (bugWorld 0)) = h_f := by
      simpa using ParHeap.restrict_refl_map h_f
    rw [hf_refl] at heq_par
    exact no_published_totHeap_with_frame_ref hw''_local hw''_no_frame
      (by rw [hw_r_eq]; exact World.le_union_left w'' _) h' heq_par

end Counterexample

/-! ## Part 3: Repaired `Swp` (`wpRepaired`) and Full Program-Logic Soundness -/

/-- Repaired semantic weakest precondition `wpRepaired u Φ : BIProp n w`:
replaces `h' : TotHeap j w'' = Heaplet j w'' w''` in `paper.tex:1855` with
`h' : ParHeap j w_r` satisfying `h'.suppWorld = w''` (equivalently `Heaplet j w'' w_r`
via `Heaplet.toParHeap`), allowing locally owned cells in `w''` to store references
into the frame world `|h_f| ⊆ w_r`! -/
noncomputable def wpRepaired {n : Nat} {w : World n} {A : SemTy}
    (u : SemTy.eval n (M A) w) (Φ : BIPred n w A) : BIProp n w where
  holds m hm w₀ hw₀ h :=
    ∀ (m' : Nat) (hm' : m' ≤ m) (w' : World m') (hw' : World.Le (w₀.restrict hm') w')
      (h_f : ParHeap m' w') (_ : ParHeap.Disjoint h_f ((h.restrict hm').map hw'))
      (h_t : TotHeap m' w'),
      TotHeap.toParHeap h_t = h_f.union ((h.restrict hm').map hw') →
      StepLift.lLift
        (u m' (Nat.le_trans hm' hm) w' (World.step_le_trans hm' hm hw₀ hw') h_t)
        (fun j hj ans =>
          ∃ (w'' : World j)
            (_ : World.Le (((h.restrict hm').map hw').restrict hj).suppWorld w'')
            (_ : World.Disjoint w'' (h_f.restrict hj).suppWorld)
            (_ : ans.1 = w''.union (h_f.restrict hj).suppWorld)
            (h' : ParHeap j ans.1),
            h'.suppWorld = w'' ∧
            ParHeap.Disjoint ((h_f.restrict hj).map ans.2.1.proof) h' ∧
            TotHeap.toParHeap ans.2.2.1 =
              ((h_f.restrict hj).map ans.2.1.proof).union h' ∧
            Φ.holds j (Nat.le_trans hj (Nat.le_trans hm' hm)) ans.1
              (World.step_le_trans hj (Nat.le_trans hm' hm)
                (World.step_le_trans hm' hm hw₀ hw') ans.2.1.proof)
              ans.2.2.2 h')
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hwp m' hm' w' hw' h_f hd h_t htot
    rcases hh with ⟨h_ext, hd_ext, rfl⟩
    let h₁_w' := (h₁.restrict (Nat.le_trans hm' hm12)).map (World.step_le_trans hm' hm12 hw12 hw')
    let h_ext' := (h_ext.restrict hm').map hw'
    have hdecomp : ((((h₁.restrict hm12).map hw12).union h_ext).restrict hm').map hw' =
        h₁_w'.union h_ext' := by
      rw [ParHeap.restrict_union, ParHeap.map_union,
        ParHeap.restrict_map_step hm' hm12 hw12 hw' h₁]
    rw [hdecomp] at hd htot
    have hd_1_ext : ParHeap.Disjoint h₁_w' h_ext' := by
      intro l
      have hde := hd_ext l
      simp only [ParHeap.map_dom, ParHeap.restrict_dom] at hde
      rcases hde with e1 | e2
      · left; simp [h₁_w', e1]
      · right; simp [h_ext', e2]
    have hd_f_ext : ParHeap.Disjoint h_f h_ext' := by
      intro l
      rcases hd l with df | d1e
      · left; exact df
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d1e
        right; exact d1e.2
    have hd_big_1 : ParHeap.Disjoint (h_f.union h_ext') h₁_w' := by
      intro l
      rcases hd l with df | d1e
      · rcases hd_1_ext l with d1 | de
        · right; exact d1
        · left; simp [df, de]
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d1e
        right; exact d1e.1
    have htot_big : TotHeap.toParHeap h_t = (h_f.union h_ext').union h₁_w' := by
      rw [htot, ← ParHeap.union_assoc, ParHeap.union_assoc h_f h₁_w' h_ext',
        ParHeap.union_comm hd_1_ext, ← ParHeap.union_assoc]
    have hstep := hwp m' (Nat.le_trans hm' hm12) w'
      (World.step_le_trans hm' hm12 hw12 hw') (h_f.union h_ext') hd_big_1 h_t htot_big
    refine StepLift.lLift_mono _ ?_ hstep
    rintro j hj ans ⟨w''₁, hw''₁_ge, hw''₁_disj, hw_r_eq, h'₁, h'₁_supp, hd_f1, hres_eq, hΦ₁⟩
    let h_ext'_j := h_ext'.restrict hj
    let h_ext'_wr := h_ext'_j.map ans.2.1.proof
    let w''₂ := w''₁.union h_ext'_j.suppWorld
    let h'₂ := h'₁.union h_ext'_wr
    have hdf_j : ParHeap.Disjoint (h_f.restrict hj) h_ext'_j := fun x => by
      simpa [h_ext'_j] using hd_f_ext x
    have hw''₁_disj_ext : World.Disjoint w''₁ h_ext'_j.suppWorld := by
      intro l
      rcases hw''₁_disj l with hn | hfn
      · left; exact hn
      · rw [ParHeap.restrict_union, ParHeap.suppWorld_union] at hfn
        simp only [World.union_cells] at hfn
        cases hfc : (h_f.restrict hj).suppWorld.cells l
        · rw [hfc] at hfn; right; exact hfn
        · rw [hfc] at hfn; contradiction
    have hw''₂_disj_f : World.Disjoint w''₂ (h_f.restrict hj).suppWorld := by
      intro l
      simp only [w''₂, World.union_cells]
      rcases hw''₁_disj l with hn1 | hfn
      · rw [hn1]
        rcases hdf_j.worldDisjoint l with d1 | d2
        · right; exact d1
        · left; exact d2
      · rw [ParHeap.restrict_union, ParHeap.suppWorld_union] at hfn
        simp only [World.union_cells] at hfn
        cases hfc : (h_f.restrict hj).suppWorld.cells l
        · right; rfl
        · rw [hfc] at hfn; contradiction
    have hd_h'1_ext : ParHeap.Disjoint h'₁ h_ext'_wr := by
      intro l
      rcases hd_f1 l with df_ext | dh1
      · rw [ParHeap.restrict_union, ParHeap.map_union] at df_ext
        simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at df_ext
        right; exact df_ext.2
      · left; exact dh1
    refine ⟨w''₂, ?_, hw''₂_disj_f, ?_, h'₂, ?_, ?_, ?_, ?_⟩
    · rw [hdecomp, ParHeap.restrict_union, ParHeap.suppWorld_union]
      intro l T hcell
      simp only [w''₂, World.union_cells] at hcell ⊢
      cases hc1 : (h₁_w'.restrict hj).suppWorld.cells l with
      | some T₁ =>
        rw [hc1] at hcell; injection hcell with hT; subst hT
        rw [hw''₁_ge l T₁ hc1]
      | none =>
        rw [hc1] at hcell
        rcases hw''₁_disj_ext l with hn1 | hn2
        · rw [hn1]; exact hcell
        · rw [hn2] at hcell; contradiction
    · rw [hw_r_eq, ParHeap.restrict_union, ParHeap.suppWorld_union]
      rw [World.union_comm hdf_j.worldDisjoint, ← World.union_assoc]
    · simp [h'₂, h_ext'_wr, h'₁_supp, w''₂]
    · intro l
      rcases hd_f1 l with df_ext | dh1
      · rw [ParHeap.restrict_union, ParHeap.map_union] at df_ext
        simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at df_ext
        left; exact df_ext.1
      · rcases hdf_j l with df | de
        · left; simpa using df
        · right; simp [h'₂, h_ext'_wr, dh1, de]
    · rw [hres_eq, ParHeap.restrict_union, ParHeap.map_union,
        ParHeap.union_assoc, ParHeap.union_comm hd_h'1_ext.symm]
    · exact Φ.mono_heap _ _ ans.2.2.2 ⟨h_ext'_wr, hd_h'1_ext, rfl⟩ hΦ₁

/-! ### Helper Combinators on `BIPred` for `wp_wand`, `wp_frame`, `wp_bind`, `wp_get`, `wp_new` -/

/-- Pointwise separating implication `fun x => Φ x -∗ Ψ x` as a `BIPred n w A`. -/
noncomputable def BIPred.wand {n : Nat} {w : World n} {A : SemTy}
    (Φ Ψ : BIPred n w A) : BIPred n w A where
  holds m hm w' hw' a h :=
    ((Φ.atVal hm hw' a).wand (Ψ.atVal hm hw' a)).holds
      m (Nat.le_refl m) w' (World.restrict_refl_le w') h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 a h₁ h₂ hh hp
    dsimp only [BIProp.wand, BIPred.atVal] at hp ⊢
    intro j hj w₃ hw₃ h' hd' hΦ'
    rcases hh with ⟨h_ext, hd_ext, rfl⟩
    let h₁_w₃ := (h₁.restrict (Nat.le_trans hj hm12)).map (World.step_le_trans hj hm12 hw12 hw₃)
    let h_ext_w₃ := (h_ext.restrict hj).map hw₃
    have hdecomp : ((((h₁.restrict hm12).map hw12).union h_ext).restrict hj).map hw₃ =
        h₁_w₃.union h_ext_w₃ := by
      rw [ParHeap.restrict_union, ParHeap.map_union,
        ParHeap.restrict_map_step hj hm12 hw12 hw₃ h₁]
    rw [hdecomp] at hd' ⊢
    have hd_h1_hp : ParHeap.Disjoint h₁_w₃ h' := by
      intro l
      rcases hd' l with d12 | d3
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12; left; exact d12.1
      · right; exact d3
    have ha_eq : SemTy.map hw₃ (SemTy.restrict hj (SemTy.map hw12 (SemTy.restrict hm12 a))) =
        SemTy.map (World.step_le_trans hj hm12 hw12 hw₃)
          (SemTy.restrict (Nat.le_trans hj hm12) a) := by
      rw [SemTy.restrict_map_comm, SemTy.map_trans,
        ← SemTy.restrict_trans_map hj hm12 (World.restrict_trans_le hj hm12 w₁) a,
        SemTy.map_trans]
    rw [ha_eq] at hΦ' ⊢
    have hΨ_base := hp j (Nat.le_trans hj hm12) w₃
      (World.step_le_trans hj hm12 hw12 hw₃) h' hd_h1_hp hΦ'
    have hd_ext_hp : ParHeap.Disjoint (h₁_w₃.union h') h_ext_w₃ := by
      intro l
      rcases hd' l with d12 | d3
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12; right; exact d12.2
      · have hde := hd_ext l
        simp only [ParHeap.map_dom, ParHeap.restrict_dom] at hde
        rcases hde with e1 | e2
        · left; simp [h₁_w₃, e1, d3]
        · right; simp [h_ext_w₃, e2]
    have hle_res : ParHeap.Le (h₁_w₃.union h') ((h₁_w₃.union h_ext_w₃).union h') := by
      refine ⟨h_ext_w₃, hd_ext_hp, ?_⟩
      rw [ParHeap.union_assoc, ParHeap.union_assoc,
        ParHeap.union_comm (show ParHeap.Disjoint h_ext_w₃ h' by
          intro l
          rcases hd' l with d12 | d3
          · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12; left; exact d12.2
          · right; exact d3)]
    exact Ψ.mono_heap _ _ _ hle_res hΨ_base

/-- Pointwise framed postcondition `fun x => R ∗ Φ x` as a `BIPred n w A`. -/
noncomputable def BIPred.sepLeft {n : Nat} {w : World n} {A : SemTy}
    (R : BIProp n w) (Φ : BIPred n w A) : BIPred n w A where
  holds m hm w' hw' a h :=
    ∃ h₁ h₂ : ParHeap m w',
      ParHeap.Disjoint h₁ h₂ ∧ h = h₁.union h₂ ∧
      R.holds m hm w' hw' h₁ ∧ Φ.holds m hm w' hw' a h₂
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 a h₁ h₂ hh ⟨p₁, p₂, hd12, heq_h₁, hr₁, hΦ₂⟩
    subst heq_h₁
    rcases hh with ⟨h_ext, hd_ext, rfl⟩
    let q₁ := (p₁.restrict hm12).map hw12
    let q₂ := ((p₂.restrict hm12).map hw12).union h_ext
    have h_union_eq : (((p₁.union p₂).restrict hm12).map hw12).union h_ext = q₁.union q₂ := by
      rw [ParHeap.restrict_union, ParHeap.map_union, ParHeap.union_assoc]
    have hd_q : ParHeap.Disjoint q₁ q₂ := by
      intro l
      rcases hd12 l with d1 | d2
      · left; simp [q₁, d1]
      · rcases hd_ext l with de1 | de2
        · simp only [ParHeap.map_dom, ParHeap.restrict_dom, ParHeap.union_dom,
            Bool.or_eq_false_iff] at de1
          left; simp [q₁, de1.1]
        · right; simp [q₂, d2, de2]
    refine ⟨q₁, q₂, hd_q, h_union_eq, R.mono hm12 hm2 hw₁ hw12 (ParHeap.le_refl q₁) hr₁, ?_⟩
    refine Φ.mono hm12 hm2 hw₁ hw12 a ⟨h_ext, ?_, rfl⟩ hΦ₂
    intro l
    rcases hd_ext l with de1 | de2
    · simp only [ParHeap.map_dom, ParHeap.restrict_dom, ParHeap.union_dom,
        Bool.or_eq_false_iff] at de1
      left; simp [de1.2]
    · right; exact de2

/-- Reindex `Φ : BIPred n w A` along `hm : m ≤ n` and `hw' : World.Le (w.restrict hm) w'`. -/
noncomputable def BIPred.reindex {n m : Nat} {w : World n} {w' : World m} {A : SemTy}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w') (Φ : BIPred n w A) :
    BIPred m w' A where
  holds j hj w₂ hw₂ a h :=
    Φ.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) a h
  mono := by
    intro j₁ j₂ hj12 hj2 w₁ w₂ hw₁ hw12 a h₁ h₂ hh hp
    exact Φ.mono hj12 (Nat.le_trans hj2 hm) (World.step_le_trans hj2 hm hw' hw₁) hw12 a hh hp

/-- Naturality predicate on Kripke functions `k : SemTy.eval n (.arr A (M B)) w`:
evaluating `k` at `(m₂, w₁, a)` and restricting to `(m₁ ≤ m₂, w₂ ≥ w₁|_m₁)` agrees with
evaluating `k` directly at `(m₁, w₂, w₂_* (a|_m₁))` (satisfied automatically by every
definable program context in `𝐅^{μ,ref}`!). -/
def IsNaturalCont {n : Nat} {w : World n} {A B : SemTy}
    (k : SemTy.eval n (.arr A (M B)) w) : Prop :=
  ∀ {m₁ m₂ : Nat} (hm12 : m₁ ≤ m₂) (hm2 : m₂ ≤ n)
    {w₁ : World m₂} {w₂ : World m₁}
    (hw₁ : World.Le (w.restrict hm2) w₁)
    (hw12 : World.Le (w₁.restrict hm12) w₂)
    (a : SemTy.eval m₂ A w₁),
    SemTy.map hw12 (SemTy.restrict hm12 (k m₂ hm2 w₁ hw₁ a)) =
      k m₁ (Nat.le_trans hm12 hm2) w₂ (World.step_le_trans hm12 hm2 hw₁ hw12)
        (SemTy.map hw12 (SemTy.restrict hm12 a))

/-- Continuation predicate `x ↦ wpRepaired (k x) Ψ` for any natural continuation `k`. -/
noncomputable def wpBindCont {n : Nat} {w : World n} {A B : SemTy}
    (k : SemTy.eval n (.arr A (M B)) w) (hnat : IsNaturalCont k)
    (Ψ : BIPred n w B) : BIPred n w A where
  holds m hm w' hw' a h :=
    (wpRepaired (k m hm w' hw' a) (Ψ.reindex hm hw')).holds
      m (Nat.le_refl m) w' (World.restrict_refl_le w') h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 a h₁ h₂ hh hp
    have hstep := (wpRepaired (k m₂ hm2 w₁ hw₁ a) (Ψ.reindex hm2 hw₁)).mono
      hm12 (Nat.le_refl m₂) (World.restrict_refl_le w₁) hw12 hh hp
    dsimp only [wpRepaired, BIPred.reindex] at hstep ⊢
    intro m' hm' w' hw' h_f hd h_t htot
    have hk_eq := hnat hm12 hm2 hw₁ hw12 a
    have hrun_eq :
        (k m₁ (Nat.le_trans hm12 hm2) w₂ (World.step_le_trans hm12 hm2 hw₁ hw12)
          (SemTy.map hw12 (SemTy.restrict hm12 a)))
          m' (Nat.le_trans hm' (Nat.le_refl m₁)) w'
          (World.step_le_trans hm' (Nat.le_refl m₁) (World.restrict_refl_le w₂) hw') h_t =
        (k m₂ hm2 w₁ hw₁ a)
          m' (Nat.le_trans hm' (Nat.le_trans hm12 (Nat.le_refl m₂))) w'
          (World.step_le_trans hm' (Nat.le_trans hm12 (Nat.le_refl m₂))
            (World.step_le_trans hm12 (Nat.le_refl m₂) (World.restrict_refl_le w₁) hw12) hw') h_t := by
      rw [← hk_eq]
      simp [SemTy.map, SemTy.restrict]
    rw [hrun_eq]
    exact hstep m' hm' w' hw' h_f hd h_t htot

/-! ### Full Soundness of `wpRepaired` (`paper.tex:741–842, 1978–2142`) -/

/-- **`wp-val` (`paper.tex:746`)**: `Φ(a) ⊢ wpRepaired (ret a) Φ`. -/
theorem wp_val {n : Nat} {w : World n} {A : SemTy}
    (a : SemTy.eval n A w) (Φ : BIPred n w A) :
    BIProp.Entails (Φ.app a) (wpRepaired (M.ret a) Φ) := by
  intro m hm w₀ hw₀ h hΦa m' hm' w' hw' h_f hd h_t htot
  simp only [M.ret, StepLift.lLift_ret]
  let h_loc := (h.restrict hm').map hw'
  have hf_refl : (h_f.restrict (Nat.le_refl m')).map (by simpa using World.le_refl w') = h_f := by
    simpa using ParHeap.restrict_refl_map h_f
  refine ⟨h_loc.suppWorld, ?_, ?_, ?_, h_loc, rfl, ?_, ?_, ?_⟩
  · simp [h_loc, ParHeap.suppWorld_restrict, World.restrict_refl]
    exact World.le_refl _
  · simp only [ParHeap.suppWorld_restrict, World.restrict_refl]
    exact hd.symm.worldDisjoint
  · simp only [ParHeap.suppWorld_restrict, World.restrict_refl]
    exact TotHeap.world_eq_of_toParHeap_union hd htot
  · rw [hf_refl]; exact hd
  · rw [hf_refl]; exact htot
  · have hΦ_m' := (Φ.app a).mono hm' hm hw₀ hw' (ParHeap.le_refl h_loc) hΦa
    dsimp only [BIPred.app] at hΦ_m'
    exact hΦ_m'

/-- **`wp-mono` (entailment consequence)**: `(Φ ⊢ Ψ) → wpRepaired e Φ ⊢ wpRepaired e Ψ`. -/
theorem wp_mono {n : Nat} {w : World n} {A : SemTy}
    (e : SemTy.eval n (M A) w) {Φ Ψ : BIPred n w A}
    (himp : ∀ m (hm : m ≤ n) (w' : World m) (hw' : World.Le (w.restrict hm) w')
              (a : SemTy.eval m A w') (h : ParHeap m w'),
              Φ.holds m hm w' hw' a h → Ψ.holds m hm w' hw' a h) :
    BIProp.Entails (wpRepaired e Φ) (wpRepaired e Ψ) := by
  intro m hm w₀ hw₀ h hwp m' hm' w' hw' h_f hd h_t htot
  refine StepLift.lLift_mono _ ?_ (hwp m' hm' w' hw' h_f hd h_t htot)
  rintro j hj ans ⟨w'', hw''_ge, hw''_disj, hw_r_eq, h', h'_supp, hd_f, hres_eq, hΦ⟩
  exact ⟨w'', hw''_ge, hw''_disj, hw_r_eq, h', h'_supp, hd_f, hres_eq,
    himp j _ ans.1 _ ans.2.2.2 h' hΦ⟩

/-- **`wp-wand` (`paper.tex:742`)**: `(∀ x, Φ x -∗ Ψ x) ∗ wpRepaired e Φ ⊢ wpRepaired e Ψ`. -/
theorem wp_wand {n : Nat} {w : World n} {A : SemTy}
    (e : SemTy.eval n (M A) w) (Φ Ψ : BIPred n w A) :
    BIProp.Entails
      ((BIProp.forallSem (BIPred.wand Φ Ψ)).sep (wpRepaired e Φ))
      (wpRepaired e Ψ) := by
  rintro m hm w₀ hw₀ h ⟨h_w, h_e, hd_we, rfl, hwand_all, hwp⟩
  intro m' hm' w' hw' h_f hd h_t htot
  let h_w' := (h_w.restrict hm').map hw'
  let h_e' := (h_e.restrict hm').map hw'
  have hdecomp : ((h_w.union h_e).restrict hm').map hw' = h_w'.union h_e' := by
    rw [ParHeap.restrict_union, ParHeap.map_union]
  rw [hdecomp] at hd htot
  have hd_we' : ParHeap.Disjoint h_w' h_e' := fun l => by
    simpa [h_w', h_e'] using hd_we l
  have hd_fw : ParHeap.Disjoint h_f h_w' := by
    intro l
    rcases hd l with df | dwe
    · left; exact df
    · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at dwe; right; exact dwe.1
  have hd_big_e : ParHeap.Disjoint (h_f.union h_w') h_e' := by
    intro l
    rcases hd l with df | dwe
    · rcases hd_we' l with dw | de
      · left; simp [df, dw]
      · right; exact de
    · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at dwe; right; exact dwe.2
  have htot_big : TotHeap.toParHeap h_t = (h_f.union h_w').union h_e' := by
    rw [htot, ParHeap.union_assoc]
  have hstep := hwp m' hm' w' hw' (h_f.union h_w') hd_big_e h_t htot_big
  refine StepLift.lLift_mono _ ?_ hstep
  rintro j hj ans ⟨w''₁, hw''₁_ge, hw''₁_disj, hw_r_eq, h'₁, h'₁_supp, hd_f1, hres_eq, hΦ₁⟩
  let h_w'_j := h_w'.restrict hj
  let h_w'_wr := h_w'_j.map ans.2.1.proof
  let w''₂ := h_w'_j.suppWorld.union w''₁
  let h'₂ := h_w'_wr.union h'₁
  have hdf_j : ParHeap.Disjoint (h_f.restrict hj) h_w'_j := fun x => by
    simpa [h_w'_j] using hd_fw x
  have hw''₁_disj_w : World.Disjoint w''₁ h_w'_j.suppWorld := by
    intro l
    rcases hw''₁_disj l with hn | hfn
    · left; exact hn
    · rw [ParHeap.restrict_union, ParHeap.suppWorld_union] at hfn
      simp only [World.union_cells] at hfn
      cases hfc : (h_f.restrict hj).suppWorld.cells l
      · rw [hfc] at hfn; right; exact hfn
      · rw [hfc] at hfn; contradiction
  have hw''₂_disj_f : World.Disjoint w''₂ (h_f.restrict hj).suppWorld := by
    intro l
    simp only [w''₂, World.union_cells]
    rcases hdf_j.worldDisjoint l with df | dw
    · right; exact df
    · rw [dw]
      rcases hw''₁_disj l with hn1 | hfn
      · left; exact hn1
      · rw [ParHeap.restrict_union, ParHeap.suppWorld_union] at hfn
        simp only [World.union_cells] at hfn
        cases hfc : (h_f.restrict hj).suppWorld.cells l
        · right; rfl
        · rw [hfc] at hfn; contradiction
  have hd_w_h'1 : ParHeap.Disjoint h_w'_wr h'₁ := by
    intro l
    rcases hd_f1 l with df_w | dh1
    · rw [ParHeap.restrict_union, ParHeap.map_union] at df_w
      simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at df_w
      left; exact df_w.2
    · right; exact dh1
  refine ⟨w''₂, ?_, hw''₂_disj_f, ?_, h'₂, ?_, ?_, ?_, ?_⟩
  · rw [hdecomp, ParHeap.restrict_union, ParHeap.suppWorld_union]
    intro l T hcell
    simp only [w''₂, World.union_cells] at hcell ⊢
    cases hcw : h_w'_j.suppWorld.cells l with
    | some _ => rw [hcw] at hcell; exact hcell
    | none => rw [hcw] at hcell; exact hw''₁_ge l T hcell
  · rw [hw_r_eq, ParHeap.restrict_union, ParHeap.suppWorld_union,
      World.union_comm hdf_j.worldDisjoint, ← World.union_assoc,
      World.union_comm hw''₁_disj_w]
  · simp [h'₂, h_w'_wr, h'₁_supp, w''₂]
  · intro l
    rcases hd_f1 l with df_w | dh1
    · rw [ParHeap.restrict_union, ParHeap.map_union] at df_w
      simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at df_w
      left; exact df_w.1
    · rcases hdf_j l with df | dw
      · left; simpa using df
      · right; simp [h'₂, h_w'_wr, dw, dh1]
  · rw [hres_eq, ParHeap.restrict_union, ParHeap.map_union, ParHeap.union_assoc]
  · have h_w_step : ((h_w.restrict (Nat.le_trans hj hm')).map
        (World.step_le_trans hj hm' hw' ans.2.1.proof)) = h_w'_wr := by
      exact (ParHeap.restrict_map_step hj hm' hw' ans.2.1.proof h_w).symm
    have hwand_inst := hwand_all j (Nat.le_trans hj hm') ans.1
      (World.step_le_trans hj hm' hw' ans.2.1.proof) h_w'_wr ans.2.2.2
      (by rw [h_w_step]; exact ParHeap.le_refl _)
    dsimp only [BIPred.wand, BIProp.wand, BIPred.atVal] at hwand_inst
    have hrefl_wr : (h_w'_wr.restrict (Nat.le_refl j)).map (World.restrict_refl_le ans.1) =
        h_w'_wr := ParHeap.restrict_refl_map h_w'_wr
    have ha_refl : SemTy.map (World.restrict_refl_le ans.1)
        (SemTy.restrict (Nat.le_refl j) ans.2.2.2) = ans.2.2.2 :=
      SemTy.restrict_refl_map _ ans.2.2.2
    have hΨ_res := hwand_inst j (Nat.le_refl j) ans.1 (World.restrict_refl_le ans.1) h'₁
      (by rw [hrefl_wr]; exact hd_w_h'1)
      (by rw [ha_refl]; exact hΦ₁)
    rw [hrefl_wr, ha_refl] at hΨ_res
    exact hΨ_res

/-- **`wp-frame` (derived directly from `wp_wand`, `paper.tex:773`)**:
`R ∗ wpRepaired e Φ ⊢ wpRepaired e (fun x => R ∗ Φ x)`. -/
theorem wp_frame {n : Nat} {w : World n} {A : SemTy}
    (R : BIProp n w) (e : SemTy.eval n (M A) w) (Φ : BIPred n w A) :
    BIProp.Entails (R.sep (wpRepaired e Φ)) (wpRepaired e (BIPred.sepLeft R Φ)) := by
  refine BIProp.entails_trans (bi_sep_mono ?_ (BIProp.entails_refl _))
    (wp_wand e Φ (BIPred.sepLeft R Φ))
  intro m hm w₀ hw₀ h hr j hj w₂ hw₂ h₂ a hh₂ j' hj' w₃ hw₃ h' hd' hΦ'
  have hr₂ := R.mono hj hm hw₀ hw₂ hh₂ hr
  have hr₃ := R.mono hj' (Nat.le_trans hj hm) (World.step_le_trans hj hm hw₀ hw₂)
    hw₃ (ParHeap.le_refl _) hr₂
  exact ⟨(h₂.restrict hj').map hw₃, h', hd', rfl, hr₃, hΦ'⟩

/-- **`wp-bind` (general semantic rule, `paper.tex:750`)**:
For any intermediate postcondition `Φ` entailing `wpRepaired (k x) Ψ`,
`wpRepaired e Φ ⊢ wpRepaired (M.bind e k) Ψ`. -/
theorem wp_bind_gen {n : Nat} {w : World n} {A B : SemTy}
    (e : SemTy.eval n (M A) w) (k : SemTy.eval n (.arr A (M B)) w)
    (Φ : BIPred n w A) (Ψ : BIPred n w B)
    (hk : ∀ m (hm : m ≤ n) (w' : World m) (hw' : World.Le (w.restrict hm) w')
            (a : SemTy.eval m A w'),
          BIProp.Entails (Φ.atVal hm hw' a)
            (wpRepaired (k m hm w' hw' a) (Ψ.reindex hm hw'))) :
    BIProp.Entails (wpRepaired e Φ) (wpRepaired (M.bind e k) Ψ) := by
  intro m hm w₀ hw₀ h hwp₁ m' hm' w' hw' h_f hd h_t htot
  dsimp only [M.bind]
  apply StepLift.lLift_bind
  refine StepLift.lLift_mono _ ?_ (hwp₁ m' hm' w' hw' h_f hd h_t htot)
  rintro j hj ans₁ ⟨w''₁, hw''₁_ge, hw''₁_disj, hw_r₁_eq, h'₁, h'₁_supp, hd_f1, hres₁_eq, hΦ₁⟩
  rw [StepLift.lLift_map]
  let hm_j : j ≤ n := Nat.le_trans hj (Nat.le_trans hm' hm)
  let hw_j : World.Le (w.restrict hm_j) ans₁.1 :=
    World.step_le_trans hj (Nat.le_trans hm' hm) (World.step_le_trans hm' hm hw₀ hw') ans₁.2.1.proof
  have hΦ_at : (Φ.atVal hm_j hw_j ans₁.2.2.2).holds j (Nat.le_refl j) ans₁.1
      (World.restrict_refl_le ans₁.1) h'₁ := by
    dsimp only [BIPred.atVal]
    rw [SemTy.restrict_refl_map _ ans₁.2.2.2]
    exact hΦ₁
  have hwp₂ := hk j hm_j ans₁.1 hw_j ans₁.2.2.2 j (Nat.le_refl j) ans₁.1
    (World.restrict_refl_le ans₁.1) h'₁ hΦ_at
  have h'₁_refl : (h'₁.restrict (Nat.le_refl j)).map (by simpa using World.le_refl ans₁.1) = h'₁ := by
    simpa using ParHeap.restrict_refl_map h'₁
  have hstep₂ := hwp₂ j (Nat.le_refl j) ans₁.1 (by simpa using World.le_refl ans₁.1)
    ((h_f.restrict hj).map ans₁.2.1.proof)
    (by rw [h'₁_refl]; exact hd_f1)
    ans₁.2.2.1
    (by rw [h'₁_refl]; exact hres₁_eq)
  refine StepLift.lLift_mono _ ?_ hstep₂
  rintro q hq ans₂ ⟨w''₂, hw''₂_ge, hw''₂_disj, hw_r₂_eq, h'₂, h'₂_supp, hd_f2, hres₂_eq, hΨ₂⟩
  rw [h'₁_refl] at hw''₂_ge
  have hf_restr_eq : ((h_f.restrict hj).map ans₁.2.1.proof).restrict hq =
      ((h_f.restrict (Nat.le_trans hq hj)).map
        (by rw [← World.restrict_trans hq hj w']; exact World.restrict_mono hq ans₁.2.1.proof)) := by
    rw [ParHeap.restrict_map_comm, ← ParHeap.restrict_trans_map hq hj h_f, ParHeap.map_trans]
  have hf_supp_eq : (((h_f.restrict hj).map ans₁.2.1.proof).restrict hq).suppWorld =
      (h_f.restrict (Nat.le_trans hq hj)).suppWorld := by
    rw [hf_restr_eq, ParHeap.suppWorld_map]
  refine ⟨w''₂, ?_, ?_, ?_, h'₂, h'₂_supp, ?_, ?_, ?_⟩
  · have hloc_tr : (((h.restrict hm').map hw').restrict (Nat.le_trans hq hj)).suppWorld =
        ((((h.restrict hm').map hw').restrict hj).suppWorld).restrict hq := by
      rw [← ParHeap.suppWorld_restrict, ← ParHeap.restrict_trans_map hq hj,
        ParHeap.suppWorld_map, ParHeap.suppWorld_restrict]
    rw [hloc_tr]
    have h1 : World.Le ((((h.restrict hm').map hw').restrict hj).suppWorld.restrict hq)
        (w''₁.restrict hq) := World.restrict_mono hq hw''₁_ge
    have h2 : (h'₁.restrict hq).suppWorld = w''₁.restrict hq := by
      rw [ParHeap.suppWorld_restrict, h'₁_supp]
    rw [← h2] at h1
    exact World.le_trans h1 hw''₂_ge
  · rw [← hf_supp_eq]; exact hw''₂_disj
  · rw [← hf_supp_eq]; exact hw_r₂_eq
  · have hf_map_eq : (((h_f.restrict hj).map ans₁.2.1.proof).restrict hq).map ans₂.2.1.proof =
        (h_f.restrict (Nat.le_trans hq hj)).map (M.reanchorAns hj ans₁.2.1.proof q hq ans₂).2.1.proof := by
      rw [hf_restr_eq, ParHeap.map_trans]
    rw [← hf_map_eq]; exact hd_f2
  · have hf_map_eq : (((h_f.restrict hj).map ans₁.2.1.proof).restrict hq).map ans₂.2.1.proof =
        (h_f.restrict (Nat.le_trans hq hj)).map (M.reanchorAns hj ans₁.2.1.proof q hq ans₂).2.1.proof := by
      rw [hf_restr_eq, ParHeap.map_trans]
    rw [← hf_map_eq]; exact hres₂_eq
  · exact hΨ₂

/-- **`wp-bind` (`paper.tex:750` single-sequent form)**:
`wpRepaired e (x ↦ wpRepaired (k x) Ψ) ⊢ wpRepaired (M.bind e k) Ψ`. -/
theorem wp_bind {n : Nat} {w : World n} {A B : SemTy}
    (e : SemTy.eval n (M A) w) (k : SemTy.eval n (.arr A (M B)) w)
    (hnat : IsNaturalCont k) (Ψ : BIPred n w B) :
    BIProp.Entails (wpRepaired e (wpBindCont k hnat Ψ)) (wpRepaired (M.bind e k) Ψ) := by
  refine wp_bind_gen e k (wpBindCont k hnat Ψ) Ψ ?_
  intro m hm w' hw' a j hj w₂ hw₂ h hp
  dsimp only [BIPred.atVal, wpBindCont] at hp
  have hmon := (wpRepaired (k j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂)
      (SemTy.map hw₂ (SemTy.restrict hj a)))
    (Ψ.reindex (Nat.le_trans hj hm) (World.step_le_trans hj hm hw' hw₂))).mono_heap
    (Nat.le_refl j) (World.restrict_refl_le w₂) (ParHeap.le_refl h) hp
  dsimp only [wpRepaired, BIPred.reindex] at hmon ⊢
  intro m' hm' w₃ hw₃ h_f hd h_t htot
  have hk_eq := hnat hj hm hw' hw₂ a
  have hrun_eq :
      (k m hm w' hw' a) m' (Nat.le_trans hm' hj) w₃
        (World.step_le_trans hm' hj hw₂ hw₃) h_t =
      (k j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂)
        (SemTy.map hw₂ (SemTy.restrict hj a))) m'
        (Nat.le_trans hm' (Nat.le_refl j)) w₃
        (World.step_le_trans hm' (Nat.le_refl j) (World.restrict_refl_le w₂) hw₃) h_t := by
    rw [← hk_eq]
    simp [SemTy.map, SemTy.restrict]
  rw [hrun_eq]
  exact hmon m' hm' w₃ hw₃ h_f hd h_t htot

/-- **`wp-step` (`paper.tex:766`)**: `▷ P ⊢ wpRepaired M.step (fun _ => P)`. -/
theorem wp_step {n : Nat} {w : World n} (P : BIProp n w) :
    BIProp.Entails P.later (wpRepaired M.step (BIPred.const SemTy.unit P)) := by
  intro m hm w₀ hw₀ h hlat m' hm' w' hw' h_f hd h_t htot
  cases m' with
  | zero => simp [M.step]
  | succ q =>
    simp only [M.step, StepLift.lLift_stepSucc, StepLift.lLift_ret]
    let h_loc := (h.restrict hm').map hw'
    let h_loc_q := h_loc.restrict (Nat.le_succ_of_le (Nat.le_refl q))
    let h_f_q := h_f.restrict (Nat.le_succ_of_le (Nat.le_refl q))
    have hd_q : ParHeap.Disjoint h_f_q h_loc_q := fun l => by
      simpa [h_f_q, h_loc_q, h_loc] using hd l
    have hlat_m' : P.later.holds (q + 1) (Nat.le_trans hm' hm) w'
        (World.step_le_trans hm' hm hw₀ hw') h_loc :=
      P.later.mono hm' hm hw₀ hw' (ParHeap.le_refl h_loc) hlat
    dsimp only [BIProp.later] at hlat_m'
    refine ⟨h_loc_q.suppWorld, World.le_refl _, hd_q.symm.worldDisjoint, ?_,
      h_loc_q, rfl, ?_, ?_, ?_⟩
    · have hw_eq := TotHeap.world_eq_of_toParHeap_union hd htot
      have hw_tr := congrArg World.trunc hw_eq
      simpa [World.trunc, ParHeap.suppWorld_restrict, h_loc_q, h_loc] using hw_tr
    · rw [ParHeap.map_refl]; exact hd_q
    · rw [ParHeap.map_refl, TotHeap.trunc_toParHeap, htot, ParHeap.restrict_union]
    · exact hlat_m'

/-- **`wp-get` (`paper.tex:1998`)**:
`[r ↦ a] ∗ ▷ ([r ↦ a] -∗ Φ a) ⊢ wpRepaired (M.get r) Φ`. -/
theorem wp_get_val {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) (a : SemTy.eval n A w) (Φ : BIPred n w A) :
    BIProp.Entails
      ((BIProp.pointsTo r a).sep
        ((BIProp.pointsTo r a).wand (Φ.app a)).later)
      (wpRepaired (M.get r) Φ) := by
  rintro m hm w₀ hw₀ h ⟨h₁, h₂, hd12, rfl, hpt, hlat_wand⟩
  intro m' hm' w' hw' h_f hd h_t htot
  cases m' with
  | zero => simp [M.get]
  | succ q =>
    simp only [M.get, StepLift.lLift_stepSucc, StepLift.lLift_ret]
    let h₁' := (h₁.restrict hm').map hw'
    let h₂' := (h₂.restrict hm').map hw'
    have hdecomp : ((h₁.union h₂).restrict hm').map hw' = h₁'.union h₂' := by
      rw [ParHeap.restrict_union, ParHeap.map_union]
    have hd12' : ParHeap.Disjoint h₁' h₂' := fun l => by
      simpa [h₁', h₂'] using hd12 l
    have hpt' : (BIProp.pointsTo r a).holds (q + 1) (Nat.le_trans hm' hm) w'
        (World.step_le_trans hm' hm hw₀ hw') h₁' :=
      (BIProp.pointsTo r a).mono hm' hm hw₀ hw' (ParHeap.le_refl h₁') hpt
    dsimp only [BIProp.pointsTo] at hpt'
    rcases hpt' with ⟨h_junk, hd_sj, hh₁'_eq⟩
    let a_w' := SemTy.map (World.step_le_trans hm' hm hw₀ hw')
      (SemTy.restrict (Nat.le_trans hm' hm) a)
    have hl_w' : w'.cells r.down.1 = some A :=
      (World.step_le_trans hm' hm hw₀ hw') r.down.1 (SemTy.nextAt (q + 1) A)
        (by simp [World.restrict_cells, r.down.2])
    -- Read `r.down.1` from `h_t` at stage `q + 1`:
    have hf_r_false : h_f.dom r.down.1 = false := by
      rcases hd r.down.1 with df | dloc
      · exact df
      · rw [hdecomp, hh₁'_eq] at dloc
        simp [ParHeap.union_dom, ParHeap.singleton_dom] at dloc
    have hget_r : CellVal.toEval (h_t.get r.down.1 A hl_w') =
        SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl q)) a_w' := by
      have htot_eq : TotHeap.toParHeap h_t =
          h_f.union (((ParHeap.singleton r.down.1 hl_w' a_w').union h_junk).union h₂') := by
        rw [htot, hdecomp, hh₁'_eq]
      have hcell_eq := ParHeap.eta_get_of_eq htot_eq r.down.1 A
        (by simp [TotHeap.toParHeap, hl_w'])
        (by simp [ParHeap.union_dom, ParHeap.singleton_dom, hl_w'])
      dsimp only [TotHeap.toParHeap] at hcell_eq
      simp only [ParHeap.union, hf_r_false, Bool.false_eq_true, ↓reduceDIte,
        ParHeap.singleton_dom, beq_self_eq_true] at hcell_eq
      have hs_val : (ParHeap.singleton r.down.1 hl_w' a_w').eta.get r.down.1 A
          (by simp [hl_w']) = CellVal.nextVal a_w' := by
        simp [ParHeap.singleton]
      have hraw : h_t.get r.down.1 A hl_w' = CellVal.nextVal a_w' :=
        hcell_eq.trans hs_val
      rw [hraw]
      simp [CellVal.nextVal]
    let hk_le : q ≤ q + 1 := Nat.le_succ_of_le (Nat.le_refl q)
    let h₁'_q := h₁'.restrict hk_le
    let h₂'_q := h₂'.restrict hk_le
    let h_loc_q := (((h₁.union h₂).restrict hm').map hw').restrict hk_le
    let h_f_q := h_f.restrict hk_le
    have hloc_q_eq : h_loc_q = h₁'_q.union h₂'_q := by
      simp [h_loc_q, ParHeap.restrict_union, ParHeap.map_union, h₁', h₂', h₁'_q, h₂'_q]
    have hd_f_loc_q : ParHeap.Disjoint h_f_q h_loc_q := fun l => by
      simpa [h_f_q, h_loc_q] using hd l
    have hd12_q : ParHeap.Disjoint h₂'_q h₁'_q := fun l => by
      simpa [h₁'_q, h₂'_q] using (hd12'.symm l)
    -- Discharge `▷` from `hlat_wand` at stage `q + 1`:
    have hlat_m' := ((BIProp.pointsTo r a).wand (Φ.app a)).later.mono
      hm' hm hw₀ hw' (ParHeap.le_refl h₂') hlat_wand
    dsimp only [BIProp.later] at hlat_m'
    have hpt_q : (BIProp.pointsTo r a).holds q _ w'.trunc _ h₁'_q :=
      (BIProp.pointsTo r a).mono_stage hk_le _ _ h₁'
        ((BIProp.pointsTo r a).mono hm' hm hw₀ hw' (ParHeap.le_refl h₁') hpt)
    have h₂'_q_refl : (h₂'_q.restrict (Nat.le_refl q)).map (World.restrict_refl_le w'.trunc) =
        h₂'_q := ParHeap.restrict_refl_map h₂'_q
    have hΦ_app := hlat_m' q (Nat.le_refl q) w'.trunc (World.restrict_refl_le w'.trunc) h₁'_q
      (by rw [h₂'_q_refl]; exact hd12_q) hpt_q
    rw [h₂'_q_refl, ParHeap.union_comm hd12_q, ← hloc_q_eq] at hΦ_app
    dsimp only [BIPred.app] at hΦ_app
    refine ⟨h_loc_q.suppWorld, World.le_refl _, hd_f_loc_q.symm.worldDisjoint, ?_,
      h_loc_q, rfl, ?_, ?_, ?_⟩
    · have hw_eq : w' = (h₁'.union h₂').suppWorld.union h_f.suppWorld := by
        have htot' : TotHeap.toParHeap h_t = h_f.union (h₁'.union h₂') := by
          rw [htot, hdecomp]
        have hd' : ParHeap.Disjoint h_f (h₁'.union h₂') := by
          rw [← hdecomp]; exact hd
        exact TotHeap.world_eq_of_toParHeap_union hd' htot'
      have htr := congrArg World.trunc hw_eq
      rw [hloc_q_eq, ParHeap.suppWorld_union]
      simpa [World.trunc, ParHeap.suppWorld_union, ParHeap.suppWorld_restrict,
        h₁'_q, h₂'_q, h_f_q] using htr
    · rw [ParHeap.map_refl]; exact hd_f_loc_q
    · rw [ParHeap.map_refl, TotHeap.trunc_toParHeap, htot, ParHeap.restrict_union]
    · have hget_r' : ∀ hl_p, CellVal.toEval (h_t.get r.down.1 A hl_p) =
          SemTy.restrict hk_le a_w' := fun _ => hget_r
      rw [hget_r']
      have ha_eq : SemTy.restrict hk_le a_w' =
          SemTy.map (World.step_le_trans (Nat.le_refl q) _
            (World.step_le_trans hk_le (Nat.le_trans hm' hm)
              (World.step_le_trans hm' hm hw₀ hw') (World.le_refl w'.trunc))
            (World.restrict_refl_le w'.trunc))
          (SemTy.restrict (Nat.le_trans (Nat.le_refl q)
            (Nat.le_of_succ_le (Nat.le_trans hm' hm))) a) := by
        dsimp only [a_w']
        rw [SemTy.restrict_map_comm,
          ← SemTy.restrict_trans_map hk_le (Nat.le_trans hm' hm)
            (World.restrict_trans_le _ _ w) a,
          SemTy.map_trans]
      rw [ha_eq]
      exact hΦ_app

/-- **`wp-set` (`paper.tex:758`, **0 `▷`s!!**)**:
`(∃ y, [r ↦ y]) ∗ ([r ↦ a] -∗ Φ ()) ⊢ wpRepaired (M.set r a) Φ` —
holds unconditionally at ALL worlds and types, INCLUDING when `a` references
frame-owned locations! -/
theorem wp_set {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) (a : SemTy.eval n A w)
    (Φ : BIPred n w SemTy.unit) :
    BIProp.Entails
      ((BIProp.pointsToSome r).sep
        ((BIProp.pointsTo r a).wand (Φ.app ⟨PUnit.unit⟩)))
      (wpRepaired (M.set r a) Φ) := by
  rintro m hm w₀ hw₀ h ⟨h₁, h₂, hd12, rfl, hsome, hwand⟩
  intro m' hm' w' hw' h_f hd h_t htot
  simp only [M.set, StepLift.lLift_ret]
  let h₁' := (h₁.restrict hm').map hw'
  let h₂' := (h₂.restrict hm').map hw'
  have hdecomp : ((h₁.union h₂).restrict hm').map hw' = h₁'.union h₂' := by
    rw [ParHeap.restrict_union, ParHeap.map_union]
  have hd12' : ParHeap.Disjoint h₁' h₂' := fun l => by
    simpa [h₁', h₂'] using hd12 l
  have hsome' := (BIProp.pointsToSome r).mono hm' hm hw₀ hw' (ParHeap.le_refl h₁') hsome
  rcases hsome' with ⟨y', h_junk, hd_sj, hh₁'_eq⟩
  let hw_total := World.step_le_trans hm' hm hw₀ hw'
  let hl_w' : w'.cells r.down.1 = some (SemTy.nextAt m' A) :=
    hw_total r.down.1 (SemTy.nextAt m' A) (by simp [World.restrict_cells, r.down.2])
  let a_w' := SemTy.map hw_total (SemTy.restrict (Nat.le_trans hm' hm) a)
  let h₁'_upd := (ParHeap.singleton r.down.1 hl_w' a_w').union h_junk
  let h'_new := h₁'_upd.union h₂'
  have hdom_h1 : ∀ l, h₁'_upd.dom l = h₁'.dom l := by
    intro l; rw [hh₁'_eq]; rfl
  have hd_upd_2 : ParHeap.Disjoint h₁'_upd h₂' := by
    intro l; rw [hdom_h1]; exact hd12' l
  have hd_f_new : ParHeap.Disjoint h_f h'_new := by
    intro l
    rcases hd l with df | dloc
    · left; exact df
    · rw [hdecomp] at dloc
      simp only [ParHeap.union_dom] at dloc ⊢
      rw [← hdom_h1] at dloc
      right; exact dloc
  have hsupp_eq : h'_new.suppWorld = (h₁'.union h₂').suppWorld := by
    apply World.ext
    intro l
    simp only [ParHeap.suppWorld, World.restrictDom_cells, h'_new, ParHeap.union_dom, hdom_h1]
  have hf_refl : (h_f.restrict (Nat.le_refl m')).map (by simpa using World.le_refl w') = h_f := by
    simpa using ParHeap.restrict_refl_map h_f
  refine ⟨h'_new.suppWorld, ?_, ?_, ?_, h'_new, rfl, ?_, ?_, ?_⟩
  · rw [hdecomp, ParHeap.suppWorld_restrict, World.restrict_refl, hsupp_eq]
    exact World.le_refl _
  · simp only [ParHeap.suppWorld_restrict, World.restrict_refl]
    exact hd_f_new.symm.worldDisjoint
  · simp only [ParHeap.suppWorld_restrict, World.restrict_refl, hsupp_eq, ← hdecomp]
    exact TotHeap.world_eq_of_toParHeap_union hd htot
  · rw [hf_refl]; exact hd_f_new
  · rw [hf_refl]
    have ha_eq : SemTy.map (World.step_le_trans hm' hm hw₀ hw')
        (SemTy.restrict (Nat.le_trans hm' hm) a) = a_w' := rfl
    rw [ha_eq]
    have htot_assoc : TotHeap.toParHeap h_t =
        (h_f.union h₂').union ((ParHeap.singleton r.down.1 hl_w' y').union h_junk) := by
      have h12_comm : h₁'.union h₂' = h₂'.union h₁' := ParHeap.union_comm hd12'
      rw [htot, hdecomp, h12_comm, hh₁'_eq, ← ParHeap.union_assoc]
    have hd_f2_loc : ParHeap.Disjoint (h_f.union h₂')
        ((ParHeap.singleton r.down.1 hl_w' y').union h_junk) := by
      intro l
      rw [← hh₁'_eq]
      rcases hd12' l with d1 | d2
      · right; exact d1
      · rcases hd l with df | dloc
        · left; simp [df, d2]
        · rw [hdecomp] at dloc
          simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at dloc
          right; exact dloc.1
    have hsplit := TotHeap.update_toParHeap_split h_t (h_f.union h₂') h_junk
      r.down.1 hl_w' y' a_w' hd_sj hd_f2_loc htot_assoc
    have hsplit_any : ∀ hl_p,
        TotHeap.toParHeap (TotHeap.update h_t r.down.1 hl_p (CellVal.nextVal a_w')) =
          (h_f.union h₂').union h₁'_upd := fun _ => hsplit
    rw [hsplit_any]
    rw [ParHeap.union_assoc, ParHeap.union_comm hd_upd_2.symm]
  · have hpt_upd : (BIProp.pointsTo r a).holds m' (Nat.le_trans hm' hm) w' hw_total h₁'_upd :=
      ⟨h_junk, hd_sj, rfl⟩
    have hΦ_unit := hwand m' hm' w' hw' h₁'_upd hd_upd_2.symm hpt_upd
    rw [ParHeap.union_comm hd_upd_2.symm] at hΦ_unit
    dsimp only [BIPred.app] at hΦ_unit
    exact hΦ_unit

/-- Precondition predicate `r ↦ ([r ↦ a] -∗ Φ r)` for `wp_new` (`paper.tex:762`). -/
noncomputable def wpNewPre {n : Nat} {w : World n} {A : SemTy}
    (a : SemTy.eval n A w) (Φ : BIPred n w (.ref A)) : BIPred n w (.ref A) where
  holds m hm w' hw' r h :=
    ((BIProp.pointsTo r (SemTy.map hw' (SemTy.restrict hm a))).wand
      (Φ.atVal hm hw' r)).holds m (Nat.le_refl m) w' (World.restrict_refl_le w') h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 r h₁ h₂ hh hp
    dsimp only [BIProp.wand, BIPred.atVal] at hp ⊢
    intro j hj w₃ hw₃ h' hd' hpt'
    rcases hh with ⟨h_ext, hd_ext, rfl⟩
    let h₁_w₃ := (h₁.restrict (Nat.le_trans hj hm12)).map (World.step_le_trans hj hm12 hw12 hw₃)
    let h_ext_w₃ := (h_ext.restrict hj).map hw₃
    have hdecomp : ((((h₁.restrict hm12).map hw12).union h_ext).restrict hj).map hw₃ =
        h₁_w₃.union h_ext_w₃ := by
      rw [ParHeap.restrict_union, ParHeap.map_union,
        ParHeap.restrict_map_step hj hm12 hw12 hw₃ h₁]
    rw [hdecomp] at hd' ⊢
    have hd_h1_hp : ParHeap.Disjoint h₁_w₃ h' := by
      intro l
      rcases hd' l with d12 | d3
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12; left; exact d12.1
      · right; exact d3
    have hr_eq : SemTy.map hw₃ (SemTy.restrict hj (SemTy.map hw12 (SemTy.restrict hm12 r))) =
        SemTy.map (World.step_le_trans hj hm12 hw12 hw₃)
          (SemTy.restrict (Nat.le_trans hj hm12) r) := by
      rcases r with ⟨⟨_, _⟩⟩; simp [SemTy.map, SemTy.restrict]
    have hpt_conv : (BIProp.pointsTo r (SemTy.map hw₁ (SemTy.restrict hm2 a))).holds j
        (Nat.le_trans (Nat.le_trans hj hm12) (Nat.le_refl m₂)) w₃
        (World.step_le_trans (Nat.le_trans hj hm12) (Nat.le_refl m₂)
          (World.restrict_refl_le w₁) (World.step_le_trans hj hm12 hw12 hw₃)) h' := by
      dsimp only [BIProp.pointsTo] at hpt' ⊢
      have ha_eq :
          SemTy.map (World.step_le_trans hj (Nat.le_refl m₁) (World.restrict_refl_le w₂) hw₃)
            (SemTy.restrict (Nat.le_trans hj (Nat.le_refl m₁))
              (SemTy.map (World.step_le_trans hm12 hm2 hw₁ hw12)
                (SemTy.restrict (Nat.le_trans hm12 hm2) a))) =
          SemTy.map (World.step_le_trans (Nat.le_trans hj hm12) (Nat.le_refl m₂)
              (World.restrict_refl_le w₁) (World.step_le_trans hj hm12 hw12 hw₃))
            (SemTy.restrict (Nat.le_trans (Nat.le_trans hj hm12) (Nat.le_refl m₂))
              (SemTy.map hw₁ (SemTy.restrict hm2 a))) := by
        simp only [SemTy.restrict_map_comm, SemTy.map_trans]
        have h_lhs_norm :
            SemTy.map (World.le_trans (World.restrict_mono (Nat.le_trans hj (Nat.le_refl m₁))
                (World.step_le_trans hm12 hm2 hw₁ hw12))
              (World.step_le_trans hj (Nat.le_refl m₁) (World.restrict_refl_le w₂) hw₃))
              (SemTy.restrict (Nat.le_trans hj (Nat.le_refl m₁))
                (SemTy.restrict (Nat.le_trans hm12 hm2) a)) =
            SemTy.map (World.step_le_trans (Nat.le_trans hj hm12) hm2 hw₁
                (World.step_le_trans hj hm12 hw12 hw₃))
              (SemTy.restrict (Nat.le_trans (Nat.le_trans hj hm12) hm2) a) := by
          have ht := SemTy.restrict_trans_map hj (Nat.le_trans hm12 hm2)
            (World.restrict_trans_le _ _ w) a
          rw [← ht, SemTy.map_trans]
        have h_rhs_norm :
            SemTy.map (World.le_trans (World.restrict_mono
                (Nat.le_trans (Nat.le_trans hj hm12) (Nat.le_refl m₂)) hw₁)
              (World.step_le_trans (Nat.le_trans hj hm12) (Nat.le_refl m₂)
                (World.restrict_refl_le w₁) (World.step_le_trans hj hm12 hw12 hw₃)))
              (SemTy.restrict (Nat.le_trans (Nat.le_trans hj hm12) (Nat.le_refl m₂))
                (SemTy.restrict hm2 a)) =
            SemTy.map (World.step_le_trans (Nat.le_trans hj hm12) hm2 hw₁
                (World.step_le_trans hj hm12 hw12 hw₃))
              (SemTy.restrict (Nat.le_trans (Nat.le_trans hj hm12) hm2) a) := by
          have ht := SemTy.restrict_trans_map (Nat.le_trans hj hm12) hm2
            (World.restrict_trans_le _ _ w) a
          rw [← ht, SemTy.map_trans]
        exact h_lhs_norm.trans h_rhs_norm.symm
      simpa only [SemTy.map_ref_val, SemTy.restrict_ref_val, ha_eq] using hpt'
    have hΦ_base := hp j (Nat.le_trans hj hm12) w₃
      (World.step_le_trans hj hm12 hw12 hw₃) h' hd_h1_hp hpt_conv
    rw [← hr_eq] at hΦ_base
    have hd_ext_hp : ParHeap.Disjoint (h₁_w₃.union h') h_ext_w₃ := by
      intro l
      rcases hd' l with d12 | d3
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12; right; exact d12.2
      · have hde := hd_ext l
        simp only [ParHeap.map_dom, ParHeap.restrict_dom] at hde
        rcases hde with e1 | e2
        · left; simp [h₁_w₃, e1, d3]
        · right; simp [h_ext_w₃, e2]
    have hle_res : ParHeap.Le (h₁_w₃.union h') ((h₁_w₃.union h_ext_w₃).union h') := by
      refine ⟨h_ext_w₃, hd_ext_hp, ?_⟩
      rw [ParHeap.union_assoc, ParHeap.union_assoc,
        ParHeap.union_comm (show ParHeap.Disjoint h_ext_w₃ h' by
          intro l
          rcases hd' l with d12 | d3
          · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12; left; exact d12.2
          · right; exact d3)]
    exact Φ.mono_heap _ _ _ hle_res hΦ_base

/-- **`wp-new` (`paper.tex:762`, **0 `▷`s!!**)**:
`(∀ r : ref A, [r ↦ a] -∗ Φ r) ⊢ wpRepaired (M.new a) Φ`. -/
theorem wp_new {n : Nat} {w : World n} {A : SemTy}
    (a : SemTy.eval n A w) (Φ : BIPred n w (.ref A)) :
    BIProp.Entails (BIProp.forallSem (wpNewPre a Φ)) (wpRepaired (M.new a) Φ) := by
  intro m hm w₀ hw₀ h hall m' hm' w' hw' h_f hd h_t htot
  simp only [M.new, StepLift.lLift_ret]
  let l_new := w'.fresh
  let T_m' := SemTy.nextAt m' A
  let w_new := w'.insert l_new T_m'
  let hle_new : World.Le w' w_new := World.le_insert_fresh w' T_m'
  have hl_new : w_new.cells l_new = some T_m' := by simp [w_new]
  let r_new : SemTy.eval m' (.ref A) w_new := ⟨⟨l_new, hl_new⟩⟩
  let hw_total := World.step_le_trans hm' hm hw₀ hw'
  let a_new := SemTy.map (World.le_trans hw_total hle_new) (SemTy.restrict (Nat.le_trans hm' hm) a)
  let h_loc := (h.restrict hm').map hw'
  let h_single := ParHeap.singleton l_new hl_new a_new
  let h'_res := (h_loc.map hle_new).union h_single
  have hf_fresh : h_f.dom l_new = false := by
    cases df : h_f.dom l_new
    · rfl
    · have hs := h_f.dom_sub l_new df
      rw [w'.cells_fresh] at hs; contradiction
  have hloc_fresh : h_loc.dom l_new = false := by
    cases dl : h_loc.dom l_new
    · rfl
    · have hs := h_loc.dom_sub l_new dl
      rw [w'.cells_fresh] at hs; contradiction
  have hd_loc_s : ParHeap.Disjoint (h_loc.map hle_new) h_single := by
    intro l
    by_cases heq : l = l_new
    · subst heq; left; simp [hloc_fresh]
    · right; simp [h_single, beq_false_of_ne heq]
  have hd_f_res : ParHeap.Disjoint (h_f.map hle_new) h'_res := by
    intro l
    by_cases heq : l = l_new
    · subst heq; left; simp [hf_fresh]
    · rcases hd l with df | dl
      · left; simpa using df
      · right
        have dl' : h_loc.dom l = false := dl
        simp [h'_res, h_single, dl', beq_false_of_ne heq]
  have hf_refl : (h_f.restrict (Nat.le_refl m')).map (by simpa using hle_new) =
      h_f.map hle_new := by
    have h0 := ParHeap.restrict_refl_map h_f
    have h1 := congrArg (ParHeap.map hle_new) h0
    rw [ParHeap.map_trans] at h1
    exact h1
  refine ⟨h'_res.suppWorld, ?_, ?_, ?_, h'_res, rfl, ?_, ?_, ?_⟩
  · simp only [ParHeap.suppWorld_restrict, World.restrict_refl, h'_res, h_loc,
      ParHeap.suppWorld_union, ParHeap.suppWorld_map]
    exact World.le_union_left _ _
  · simp only [ParHeap.suppWorld_restrict, World.restrict_refl]
    have hfs : (h_f.map hle_new).suppWorld = h_f.suppWorld := ParHeap.suppWorld_map hle_new h_f
    rw [← hfs]
    exact hd_f_res.symm.worldDisjoint
  · simp only [ParHeap.suppWorld_restrict, World.restrict_refl]
    have htot_new := TotHeap.alloc_toParHeap_split h_t h_f h_loc htot a_new
    have hw_eq := TotHeap.world_eq_of_toParHeap_union hd_f_res htot_new
    rw [ParHeap.suppWorld_map] at hw_eq
    exact hw_eq
  · rw [hf_refl]; exact hd_f_res
  · rw [hf_refl]
    exact TotHeap.alloc_toParHeap_split h_t h_f h_loc htot a_new
  · have h_loc_step : (h.restrict hm').map (World.step_le_trans (Nat.le_refl m') hm' hw'
        (World.le_trans (World.restrict_refl_le w') hle_new)) = h_loc.map hle_new := by
      dsimp only [h_loc]
      rw [ParHeap.map_trans]
    have hall_inst := hall m' hm' w_new
      (World.le_trans (World.restrict_mono hm' (World.le_refl w₀)) (World.le_trans hw' hle_new))
      (h_loc.map hle_new) r_new
      (by simpa [h_loc, ParHeap.map_trans] using ParHeap.le_refl (h_loc.map hle_new))
    dsimp only [wpNewPre, BIProp.wand, BIPred.atVal] at hall_inst
    have hrefl_loc : ((h_loc.map hle_new).restrict (Nat.le_refl m')).map
        (World.restrict_refl_le w_new) = h_loc.map hle_new :=
      ParHeap.restrict_refl_map _
    have hpt_single : (BIProp.pointsTo r_new
        (SemTy.map (World.step_le_trans hm' hm hw₀
          (World.le_trans (World.restrict_mono hm' (World.le_refl w₀)) (World.le_trans hw' hle_new)))
          (SemTy.restrict (Nat.le_trans hm' hm) a))).holds m'
        (Nat.le_refl m') w_new (World.restrict_refl_le w_new) h_single := by
      dsimp only [BIProp.pointsTo]
      have ha_refl : SemTy.map (World.restrict_refl_le w_new)
          (SemTy.restrict (Nat.le_refl m')
            (SemTy.map (World.step_le_trans hm' hm hw₀
              (World.le_trans (World.restrict_mono hm' (World.le_refl w₀))
                (World.le_trans hw' hle_new)))
              (SemTy.restrict (Nat.le_trans hm' hm) a))) = a_new := by
        rw [SemTy.restrict_refl_map]
      simpa only [r_new, ha_refl] using ParHeap.le_refl h_single
    have hΦ_res := hall_inst m' (Nat.le_refl m') w_new (World.restrict_refl_le w_new)
      h_single (by rw [hrefl_loc]; exact hd_loc_s) hpt_single
    have hr_refl : SemTy.map (World.restrict_refl_le w_new)
        (SemTy.restrict (Nat.le_refl m') r_new) = r_new :=
      SemTy.restrict_refl_map _ r_new
    rw [hrefl_loc, hr_refl] at hΦ_res
    exact hΦ_res

/-- **Positive Contrast Theorem (`wpRepaired` verifies the exact frame-reference `set` and `get`
programs where `wpPublishedAt` failed!)**: -/
theorem repaired_wp_set_and_get_frame_ref_sound :
    (wpRepaired (M.set (rLocal 0) (rFrame 0))
      (BIPred.const SemTy.unit (BIProp.top 1 (bugWorld 0)))).holds
        1 (Nat.le_refl 1) (bugWorld 0) (World.restrict_refl_le (bugWorld 0)) (bugLocalHeap 0) ∧
    (wpRepaired (M.get (rLocal 1))
      (BIPred.const (.ref SemTy.nat) (BIProp.top 2 (bugWorld 1)))).holds
        2 (Nat.le_refl 2) (bugWorld 1) (World.restrict_refl_le (bugWorld 1)) (bugLocalHeap 1) := by
  constructor
  · exact wp_set (rLocal 0) (rFrame 0) (BIPred.const SemTy.unit (BIProp.top 1 (bugWorld 0)))
      1 (Nat.le_refl 1) (bugWorld 0) (World.restrict_refl_le (bugWorld 0)) (bugLocalHeap 0)
      published_wp_set_frame_ref_unsound.1
  · exact wp_get_val (rLocal 1) (rFrame 1) (BIPred.const (.ref SemTy.nat) (BIProp.top 2 (bugWorld 1)))
      2 (Nat.le_refl 2) (bugWorld 1) (World.restrict_refl_le (bugWorld 1)) (bugLocalHeap 1)
      published_wp_get_frame_ref_unsound.1

/-! ### Fibrational Reindexing (`BIProp.reindex`), Existential `wp_get`, `wp_step_seq`, & `wp_rec` -/

@[ext]
theorem BIPred.ext {n : Nat} {w : World n} {A : SemTy} {Φ Ψ : BIPred n w A}
    (h : ∀ m (hm : m ≤ n) (w' : World m) (hw' : World.Le (w.restrict hm) w')
           (a : SemTy.eval m A w') (hp : ParHeap m w'),
           Φ.holds m hm w' hw' a hp ↔ Ψ.holds m hm w' hw' a hp) : Φ = Ψ := by
  cases Φ; cases Ψ
  congr
  funext m hm w' hw' a hp
  exact propext (h m hm w' hw' a hp)

/-- Reindex `P : BIProp n w` along `hm : m ≤ n` and `hw' : World.Le (w.restrict hm) w'`. -/
noncomputable def BIProp.reindex {n m : Nat} {w : World n} {w' : World m}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w') (P : BIProp n w) : BIProp m w' where
  holds j hj w₂ hw₂ h :=
    P.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) h
  mono := by
    intro j₁ j₂ hj12 hj2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hp
    exact P.mono hj12 (Nat.le_trans hj2 hm) (World.step_le_trans hj2 hm hw' hw₁) hw12 hh hp

@[simp]
theorem BIProp.reindex_sep {n m : Nat} {w : World n} {w' : World m}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w') (P Q : BIProp n w) :
    (P.sep Q).reindex hm hw' = (P.reindex hm hw').sep (Q.reindex hm hw') := rfl

@[simp]
theorem BIProp.reindex_wand {n m : Nat} {w : World n} {w' : World m}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w') (P Q : BIProp n w) :
    (P.wand Q).reindex hm hw' = (P.reindex hm hw').wand (Q.reindex hm hw') := rfl

@[simp]
theorem BIProp.reindex_later {n m : Nat} {w : World n} {w' : World m}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w') (P : BIProp n w) :
    P.later.reindex hm hw' = (P.reindex hm hw').later := by
  ext j _ _ _ _
  cases j <;> rfl

theorem SemTy.map_restrict_map_restrict {n m j : Nat} {A : SemTy}
    {w : World n} {w' : World m} {w₂ : World j}
    (hj : j ≤ m) (hm : m ≤ n)
    (hw' : World.Le (w.restrict hm) w') (hw₂ : World.Le (w'.restrict hj) w₂)
    (a : SemTy.eval n A w) :
    SemTy.map hw₂ (SemTy.restrict hj (SemTy.map hw' (SemTy.restrict hm a))) =
      SemTy.map (World.step_le_trans hj hm hw' hw₂) (SemTy.restrict (Nat.le_trans hj hm) a) := by
  rw [SemTy.restrict_map_comm,
    ← SemTy.restrict_trans_map hj hm (World.restrict_trans_le hj hm w) a,
    SemTy.map_trans, SemTy.map_trans]

@[simp]
theorem BIProp.reindex_pointsTo {n m : Nat} {w : World n} {w' : World m} {A : SemTy}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w')
    (r : SemTy.eval n (.ref A) w) (a : SemTy.eval n A w) :
    (BIProp.pointsTo r a).reindex hm hw' =
      BIProp.pointsTo (SemTy.map hw' (SemTy.restrict hm r))
        (SemTy.map hw' (SemTy.restrict hm a)) := by
  ext j hj w₂ hw₂ h
  simp only [BIProp.reindex, BIProp.pointsTo, SemTy.map_ref_val, SemTy.restrict_ref_val,
    SemTy.map_restrict_map_restrict]

@[simp]
theorem BIPred.reindex_app {n m : Nat} {w : World n} {w' : World m} {A : SemTy}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w')
    (Φ : BIPred n w A) (a : SemTy.eval n A w) :
    (Φ.app a).reindex hm hw' =
      (Φ.reindex hm hw').app (SemTy.map hw' (SemTy.restrict hm a)) := by
  ext j hj w₂ hw₂ h
  simp only [BIProp.reindex, BIPred.app, BIPred.reindex, SemTy.map_restrict_map_restrict]

@[simp]
theorem BIPred.reindex_reindex {n m₁ m₂ : Nat} {w : World n} {w₁ : World m₂} {w₂ : World m₁}
    {A : SemTy} (hm12 : m₁ ≤ m₂) (hm2 : m₂ ≤ n)
    (hw₁ : World.Le (w.restrict hm2) w₁) (hw12 : World.Le (w₁.restrict hm12) w₂)
    (Φ : BIPred n w A) :
    (Φ.reindex hm2 hw₁).reindex hm12 hw12 =
      Φ.reindex (Nat.le_trans hm12 hm2) (World.step_le_trans hm12 hm2 hw₁ hw12) := rfl

@[simp]
theorem wpRepaired_reindex {n m : Nat} {w : World n} {w' : World m} {A : SemTy}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w')
    (u : SemTy.eval n (M A) w) (Φ : BIPred n w A) :
    (wpRepaired u Φ).reindex hm hw' =
      wpRepaired (SemTy.map hw' (SemTy.restrict hm u)) (Φ.reindex hm hw') := by
  ext j hj w₂ hw₂ h
  simp only [BIProp.reindex, wpRepaired, SemTy.map, SemTy.restrict, BIPred.reindex]

/-- Precondition predicate `x ↦ [r ↦ x] ∗ ▷([r ↦ x] -∗ Φ x)` for `wp_get` (`paper.tex:754`). -/
noncomputable def wpGetPre {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) (Φ : BIPred n w A) : BIPred n w A where
  holds m hm w' hw' a h :=
    let r' := SemTy.map hw' (SemTy.restrict hm r)
    ((BIProp.pointsTo r' a).sep
      (((BIProp.pointsTo r' a).wand ((Φ.reindex hm hw').app a)).later)).holds
        m (Nat.le_refl m) w' (World.restrict_refl_le w') h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 a h₁ h₂ hh hp
    let r₁ := SemTy.map hw₁ (SemTy.restrict hm2 r)
    let P₁ := (BIProp.pointsTo r₁ a).sep
      (((BIProp.pointsTo r₁ a).wand ((Φ.reindex hm2 hw₁).app a)).later)
    have hmon : (P₁.reindex hm12 hw12).holds m₁ (Nat.le_refl m₁) w₂
        (World.restrict_refl_le w₂) h₂ :=
      P₁.mono hm12 (Nat.le_refl m₂) (World.restrict_refl_le w₁) hw12 hh hp
    have hr_eq : SemTy.map hw12 (SemTy.restrict hm12 r₁) =
        SemTy.map (World.step_le_trans hm12 hm2 hw₁ hw12) (SemTy.restrict (Nat.le_trans hm12 hm2) r) :=
      SemTy.map_restrict_map_restrict hm12 hm2 hw₁ hw12 r
    simpa only [P₁, BIProp.reindex_sep, BIProp.reindex_later, BIProp.reindex_wand,
      BIProp.reindex_pointsTo, BIPred.reindex_app, BIPred.reindex_reindex, hr_eq] using hmon

/-- **`wp-get` (`paper.tex:754`, existential form)**:
`(∃ x : A, [r ↦ x] ∗ ▷([r ↦ x] -∗ Φ x)) ⊢ wpRepaired (M.get r) Φ`. -/
theorem wp_get {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) (Φ : BIPred n w A) :
    BIProp.Entails (BIProp.existsSem (wpGetPre r Φ)) (wpRepaired (M.get r) Φ) := by
  rintro m hm w₀ hw₀ h ⟨a₀, hpre⟩
  have hwp₀ := wp_get_val (SemTy.map hw₀ (SemTy.restrict hm r)) a₀ (Φ.reindex hm hw₀)
    m (Nat.le_refl m) w₀ (World.restrict_refl_le w₀) h hpre
  intro m' hm' w' hw' h_f hd h_t htot
  have hget_eq :
      M.get r m' (Nat.le_trans hm' hm) w' (World.step_le_trans hm' hm hw₀ hw') h_t =
      M.get (SemTy.map hw₀ (SemTy.restrict hm r)) m'
        (Nat.le_trans hm' (Nat.le_refl m)) w'
        (World.step_le_trans hm' (Nat.le_refl m) (World.restrict_refl_le w₀) hw') h_t := by
    rcases r with ⟨⟨_, _⟩⟩
    simp only [SemTy.map, SemTy.restrict]
    cases m' <;> rfl
  rw [hget_eq]
  exact hwp₀ m' hm' w' hw' h_f hd h_t htot

/-- Sequential guarded-step rule: `▷ (wpRepaired c Ψ) ⊢ wpRepaired (M.seq M.step c) Ψ`. -/
theorem wp_step_seq {n : Nat} {w : World n} {A : SemTy}
    (c : SemTy.eval n (M A) w) (Ψ : BIPred n w A) :
    BIProp.Entails (wpRepaired c Ψ).later (wpRepaired (M.seq M.step c) Ψ) := by
  refine BIProp.entails_trans (wp_step (wpRepaired c Ψ))
    (wp_bind_gen M.step (fun _ hm' _ hw'' _ => SemTy.map hw'' (SemTy.restrict hm' c))
      (BIPred.const SemTy.unit (wpRepaired c Ψ)) Ψ ?_)
  intro m hm w' hw' _ j hj w₂ hw₂ h hp
  dsimp only [BIPred.atVal, BIPred.const] at hp
  have h_eq := wpRepaired_reindex hm hw' c Ψ
  have hp' : ((wpRepaired c Ψ).reindex hm hw').holds j hj w₂ hw₂ h := hp
  rw [h_eq] at hp'
  exact hp'

/-- `M.recFn.loop` agrees with fibrational restriction/transport of `M.recFn body`. -/
theorem M.recFn_loop_eq {n p : Nat} {w : World n} {wp : World p} {A B : SemTy}
    (body : SemTy.eval n (.arr (.arr A (M B)) (.arr A (M B))) w)
    (hp : p ≤ n) (hwp : World.Le (w.restrict hp) wp) :
    M.recFn.loop body p hp wp hwp = SemTy.map hwp (SemTy.restrict hp (M.recFn body)) := by
  funext m hm w' hw' a j hj w₂ hw₂ h₂
  unfold SemTy.map
  unfold SemTy.restrict
  cases p with
  | zero =>
    cases m with
    | zero =>
      cases j with
      | zero => cases n <;> simp [M.recFn, M.recFn.loop]
      | succ _ => omega
    | succ _ => omega
  | succ k₁ =>
    cases n with
    | zero => omega
    | succ k₂ =>
      cases j <;> simp [M.recFn, M.recFn.loop]

/-- `M.recFn body` is unconditionally a natural Kripke continuation (`IsNaturalCont`)! -/
theorem M.recFn_isNatural {n : Nat} {w : World n} {A B : SemTy}
    (body : SemTy.eval n (.arr (.arr A (M B)) (.arr A (M B))) w) :
    IsNaturalCont (M.recFn body) := by
  intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 a
  funext j hj w₃ hw₃ h₃
  have hlhs : SemTy.map hw12 (SemTy.restrict hm12 (M.recFn body m₂ hm2 w₁ hw₁ a))
      j hj w₃ hw₃ h₃ =
      M.recFn body m₂ hm2 w₁ hw₁ a j (Nat.le_trans hj hm12) w₃
        (World.step_le_trans hj hm12 hw12 hw₃) h₃ := by
    simp [SemTy.map, SemTy.restrict]
  rw [hlhs]
  cases j with
  | zero =>
    cases n with
    | zero =>
      cases m₂ with
      | zero =>
        cases m₁ with
        | zero => simp [M.recFn, M.recFn.loop]
        | succ _ => omega
      | succ _ => omega
    | succ _ => simp [M.recFn, M.recFn.loop]
  | succ q =>
    cases n with
    | zero => omega
    | succ k =>
      simp only [M.recFn, M.recFn.loop]
      rw [← SemTy.map_restrict_map_restrict hj hm12 hw12 hw₃ a]

/-- Curry `Post : BIPred n w (.prod A B)` at input `a : SemTy.eval m A w'`. -/
noncomputable def BIPred.curry {n m : Nat} {w : World n} {w' : World m} {A B : SemTy}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w')
    (Post : BIPred n w (.prod A B)) (a : SemTy.eval m A w') : BIPred m w' B where
  holds j hj w₂ hw₂ b h :=
    Post.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂)
      (SemTy.map hw₂ (SemTy.restrict hj a), b) h
  mono := by
    intro j₁ j₂ hj12 hj2 w₁ w₂ hw₁ hw12 b h₁ h₂ hh hp
    have hmon := Post.mono hj12 (Nat.le_trans hj2 hm)
      (World.step_le_trans hj2 hm hw' hw₁) hw12
      (SemTy.map hw₁ (SemTy.restrict hj2 a), b) hh hp
    simpa only [SemTy.restrict, SemTy.map, SemTy.map_restrict_map_restrict] using hmon

@[simp]
theorem BIPred.curry_reindex {n m₁ m₂ : Nat} {w : World n} {w₁ : World m₂} {w₂ : World m₁}
    {A B : SemTy} (hm12 : m₁ ≤ m₂) (hm2 : m₂ ≤ n)
    (hw₁ : World.Le (w.restrict hm2) w₁) (hw12 : World.Le (w₁.restrict hm12) w₂)
    (Post : BIPred n w (.prod A B)) (a : SemTy.eval m₂ A w₁) :
    (Post.curry hm2 hw₁ a).reindex hm12 hw12 =
      Post.curry (Nat.le_trans hm12 hm2) (World.step_le_trans hm12 hm2 hw₁ hw12)
        (SemTy.map hw12 (SemTy.restrict hm12 a)) := by
  ext j hj w₃ hw₃ b h
  simp only [BIPred.reindex, BIPred.curry, SemTy.map_restrict_map_restrict]

/-- Call specification predicate `x ↦ (Pre x -∗ wpRepaired (f x) {y. Post(x, y)})`
for any natural function `f : A → M B`. -/
noncomputable def wpCallPred {n : Nat} {w : World n} {A B : SemTy}
    (f : SemTy.eval n (.arr A (M B)) w) (hnat : IsNaturalCont f)
    (Pre : BIPred n w A) (Post : BIPred n w (.prod A B)) : BIPred n w A where
  holds m hm w' hw' a h :=
    ((Pre.atVal hm hw' a).wand
      (wpRepaired (f m hm w' hw' a) (Post.curry hm hw' a))).holds
        m (Nat.le_refl m) w' (World.restrict_refl_le w') h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 a h₁ h₂ hh hp
    let P₁ := (Pre.atVal hm2 hw₁ a).wand
      (wpRepaired (f m₂ hm2 w₁ hw₁ a) (Post.curry hm2 hw₁ a))
    have hmon : (P₁.reindex hm12 hw12).holds m₁ (Nat.le_refl m₁) w₂
        (World.restrict_refl_le w₂) h₂ :=
      P₁.mono hm12 (Nat.le_refl m₂) (World.restrict_refl_le w₁) hw12 hh hp
    have hat_eq : (Pre.atVal hm2 hw₁ a).reindex hm12 hw12 =
        Pre.atVal (Nat.le_trans hm12 hm2) (World.step_le_trans hm12 hm2 hw₁ hw12)
          (SemTy.map hw12 (SemTy.restrict hm12 a)) := by
      ext j hj w₃ hw₃ h'
      simp only [BIProp.reindex, BIPred.atVal, SemTy.map_restrict_map_restrict]
    have hf_eq := hnat hm12 hm2 hw₁ hw12 a
    simpa only [P₁, BIProp.reindex_wand, hat_eq, wpRepaired_reindex,
      BIPred.curry_reindex, hf_eq] using hmon

/-- Universal specification `∀ x : A, Pre x -∗ wpRepaired ((M.recFn body) x) {y. Post(x, y)}`
for guarded recursive functions (`paper.tex:836–842`). -/
noncomputable def wpRecSpec {n : Nat} {w : World n} {A B : SemTy}
    (body : SemTy.eval n (.arr (.arr A (M B)) (.arr A (M B))) w)
    (Pre : BIPred n w A) (Post : BIPred n w (.prod A B)) : BIProp n w :=
  BIProp.forallSem (wpCallPred (M.recFn body) (M.recFn_isNatural body) Pre Post)

/-- **`wp-rec` (`paper.tex:828–842`, proved via Löb induction `bi_loeb_entails`)**:
If at every world `(m, w')` and input `a`, assuming `R` and the recursive specification
`wpRecSpec body Pre Post` suffices to prove `Pre a -∗ wpRepaired (body (recFn body) a) (Post a)`,
then `▷ R ⊢ wpRecSpec body Pre Post`! -/
theorem wp_rec {n : Nat} {w : World n} {A B : SemTy}
    (body : SemTy.eval n (.arr (.arr A (M B)) (.arr A (M B))) w)
    (R : BIProp n w) (Pre : BIPred n w A) (Post : BIPred n w (.prod A B))
    (hbody : ∀ m (hm : m ≤ n) (w' : World m) (hw' : World.Le (w.restrict hm) w')
               (a : SemTy.eval m A w'),
             BIProp.Entails
               ((R.reindex hm hw').and ((wpRecSpec body Pre Post).reindex hm hw'))
               ((Pre.atVal hm hw' a).wand
                 (wpRepaired
                   (body m hm w' hw' (SemTy.map hw' (SemTy.restrict hm (M.recFn body)))
                     m (Nat.le_refl m) w' (by simpa using World.le_refl w') a)
                   (Post.curry hm hw' a)))) :
    BIProp.Entails R.later (wpRecSpec body Pre Post) := by
  apply bi_loeb_entails
  rintro m hm w₀ hw₀ h ⟨hR_lat, hSpec_lat⟩
  intro j hj w₁ hw₁ h₁ a hh₁
  dsimp only [wpCallPred, BIProp.wand]
  intro j' hj' w₂ hw₂ h_pre hd_pre hPre
  intro m' hm' w' hw' h_f hd_f h_t htot
  cases m' with
  | zero =>
    cases n with
    | zero =>
      cases j with
      | zero => simp [M.recFn, M.recFn.loop]
      | succ _ => omega
    | succ _ => simp [M.recFn, M.recFn.loop]
  | succ q =>
    cases n with
    | zero => omega
    | succ k =>
      simp only [M.recFn, M.recFn.loop, StepLift.lLift_stepSucc, StepLift.lLift_map]
      let h₁_w₂ := (h₁.restrict hj').map hw₂
      let h₁_w' := (h₁_w₂.restrict hm').map hw'
      let h_pre_w' := (h_pre.restrict hm').map hw'
      have hdecomp_w' : ((h₁_w₂.union h_pre).restrict hm').map hw' = h₁_w'.union h_pre_w' := by
        rw [ParHeap.restrict_union, ParHeap.map_union]
      let hk_le : q ≤ q + 1 := Nat.le_succ_of_le (Nat.le_refl q)
      let hq_le_n : q ≤ k + 1 :=
        Nat.le_trans hk_le (Nat.le_trans hm' (Nat.le_trans hj' (Nat.le_trans hj hm)))
      let hw_all : World.Le ((w.restrict (Nat.le_trans hm' (Nat.le_trans hj' (Nat.le_trans hj hm))))) w' :=
        World.step_le_trans hm' _ (World.step_le_trans hj' _ (World.step_le_trans hj hm hw₀ hw₁) hw₂) hw'
      let hw_trunc : World.Le (w.restrict hq_le_n) w'.trunc :=
        World.step_le_trans hk_le _ hw_all (World.le_refl w'.trunc)
      have hR_m' : R.later.holds (q + 1) _ w' hw_all h₁_w' :=
        R.later.mono hm' _ _ hw' (ParHeap.le_refl _)
          (R.later.mono hj' _ _ hw₂ (ParHeap.le_refl _)
            (R.later.mono hj hm hw₀ hw₁ hh₁ hR_lat))
      have hSpec_m' : (wpRecSpec body Pre Post).later.holds (q + 1) _ w' hw_all h₁_w' :=
        (wpRecSpec body Pre Post).later.mono hm' _ _ hw' (ParHeap.le_refl _)
          ((wpRecSpec body Pre Post).later.mono hj' _ _ hw₂ (ParHeap.le_refl _)
            ((wpRecSpec body Pre Post).later.mono hj hm hw₀ hw₁ hh₁ hSpec_lat))
      dsimp only [BIProp.later] at hR_m' hSpec_m'
      let a_q := SemTy.restrict hk_le
        (SemTy.map (World.step_le_trans hm' hj' hw₂ hw') (SemTy.restrict (Nat.le_trans hm' hj') a))
      have hwand_q := hbody q hq_le_n w'.trunc hw_trunc a_q
        q (Nat.le_refl q) w'.trunc (World.restrict_refl_le w'.trunc) (h₁_w'.restrict hk_le)
        ⟨hR_m', hSpec_m'⟩
      dsimp only [BIProp.wand] at hwand_q
      have h₁_q_refl : ((h₁_w'.restrict hk_le).restrict (Nat.le_refl q)).map
          (World.restrict_refl_le w'.trunc) = h₁_w'.restrict hk_le :=
        ParHeap.restrict_refl_map _
      have hd_1_pre_q : ParHeap.Disjoint (h₁_w'.restrict hk_le) (h_pre_w'.restrict hk_le) := by
        intro l
        simpa [h₁_w', h₁_w₂, h_pre_w'] using hd_pre l
      have hPre_q : (Pre.atVal hq_le_n hw_trunc a_q).holds q (Nat.le_refl q) w'.trunc
          (World.restrict_refl_le w'.trunc) (h_pre_w'.restrict hk_le) := by
        have hPre_step := Pre.mono hk_le _ _ (World.le_refl w'.trunc)
          (SemTy.map hw' (SemTy.restrict hm' (SemTy.map hw₂ (SemTy.restrict hj' a))))
          (by rw [ParHeap.map_refl]; exact ParHeap.le_refl _)
          (Pre.mono hm' _ _ hw' (SemTy.map hw₂ (SemTy.restrict hj' a)) (ParHeap.le_refl _) hPre)
        dsimp only [BIPred.atVal] at hPre ⊢
        have ha_refl : SemTy.map (World.restrict_refl_le w'.trunc) (SemTy.restrict (Nat.le_refl q) a_q) = a_q :=
          SemTy.restrict_refl_map _ a_q
        rw [ha_refl]
        simpa only [a_q, SemTy.map_refl, SemTy.map_restrict_map_restrict] using hPre_step
      have hwp_body := hwand_q q (Nat.le_refl q) w'.trunc (World.restrict_refl_le w'.trunc)
        (h_pre_w'.restrict hk_le) (by rw [h₁_q_refl]; exact hd_1_pre_q) hPre_q
      rw [h₁_q_refl] at hwp_body
      rw [M.recFn_loop_eq]
      let h_loc_q := (h₁_w'.restrict hk_le).union (h_pre_w'.restrict hk_le)
      have hloc_q_eq : (((h₁_w₂.union h_pre).restrict hm').map hw').restrict hk_le = h_loc_q := by
        rw [hdecomp_w', ParHeap.restrict_union]
      have hloc_q_refl : (h_loc_q.restrict (Nat.le_refl q)).map (by simpa using World.le_refl w'.trunc) =
          h_loc_q := by
        simpa using ParHeap.restrict_refl_map h_loc_q
      have hd_f_q : ParHeap.Disjoint (h_f.restrict hk_le) h_loc_q := by
        intro l
        rw [← hloc_q_eq]
        simpa [h₁_w₂] using hd_f l
      have htot_q : TotHeap.toParHeap (TotHeap.trunc h_t) =
          (h_f.restrict hk_le).union h_loc_q := by
        rw [TotHeap.trunc_toParHeap, htot, ParHeap.restrict_union, hloc_q_eq]
      have hstep_q := hwp_body q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
        (h_f.restrict hk_le) (by rw [hloc_q_refl]; exact hd_f_q)
        (TotHeap.trunc h_t) (by rw [hloc_q_refl]; exact htot_q)
      refine StepLift.lLift_mono _ ?_ hstep_q
      rintro r hr ans ⟨w'', hw''_ge, hw''_disj, hw_r_eq, h', h'_supp, hd_fr, hres_eq, hPost_r⟩
      rw [hloc_q_refl] at hw''_ge
      have hloc_supp : ((((h₁_w₂.union h_pre).restrict hm').map hw').restrict
          (Nat.le_trans hr hk_le)).suppWorld = (h_loc_q.restrict hr).suppWorld := by
        rw [← hloc_q_eq, ← ParHeap.restrict_trans_map hr hk_le, ParHeap.suppWorld_map]
      have hf_supp : (h_f.restrict (Nat.le_trans hr hk_le)).suppWorld =
          ((h_f.restrict hk_le).restrict hr).suppWorld := by
        rw [← ParHeap.restrict_trans_map hr hk_le h_f, ParHeap.suppWorld_map]
      have hf_map_eq : ((h_f.restrict hk_le).restrict hr).map ans.2.1.proof =
          (h_f.restrict (Nat.le_trans hr hk_le)).map
            (M.reanchorAns hk_le (World.le_refl w'.trunc) r hr ans).2.1.proof := by
        rw [← ParHeap.restrict_trans_map hr hk_le h_f, ParHeap.map_trans]
      refine ⟨w'', ?_, ?_, ?_, h', h'_supp, ?_, ?_, ?_⟩
      · rw [hloc_supp]; exact hw''_ge
      · rw [hf_supp]; exact hw''_disj
      · rw [hf_supp]; exact hw_r_eq
      · rw [← hf_map_eq]; exact hd_fr
      · rw [← hf_map_eq]; exact hres_eq
      · dsimp only [BIPred.curry] at hPost_r ⊢
        have ha_r_eq :
            SemTy.map ans.2.1.proof (SemTy.restrict hr a_q) =
            SemTy.map (World.step_le_trans (Nat.le_trans hr hk_le) (Nat.le_trans hm' hj')
                (World.step_le_trans hm' hj' hw₂ hw')
                (M.reanchorAns hk_le (World.le_refl w'.trunc) r hr ans).2.1.proof)
              (SemTy.restrict (Nat.le_trans (Nat.le_trans hr hk_le) (Nat.le_trans hm' hj')) a) := by
          let x := SemTy.map (World.step_le_trans hm' hj' hw₂ hw') (SemTy.restrict (Nat.le_trans hm' hj') a)
          have htr := congrArg
            (SemTy.map (M.reanchorAns hk_le (World.le_refl w'.trunc) r hr ans).2.1.proof)
            (SemTy.restrict_trans_map hr hk_le (World.restrict_trans_le hr hk_le w') x)
          rw [SemTy.map_trans] at htr
          have hlhs : SemTy.map ans.2.1.proof (SemTy.restrict hr a_q) =
              SemTy.map (World.le_trans (World.restrict_trans_le hr hk_le w')
                (M.reanchorAns hk_le (World.le_refl w'.trunc) r hr ans).2.1.proof)
                (SemTy.restrict hr (SemTy.restrict hk_le x)) := rfl
          have hrhs := SemTy.map_restrict_map_restrict (Nat.le_trans hr hk_le)
            (Nat.le_trans hm' hj') (World.step_le_trans hm' hj' hw₂ hw')
            (M.reanchorAns hk_le (World.le_refl w'.trunc) r hr ans).2.1.proof a
          exact (hlhs.trans htr).trans hrhs
        simpa only [ha_r_eq] using hPost_r

end Tulip
