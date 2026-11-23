-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import TulipModel.Adequacy

/-!
# End-to-End Higher-Order Store Case Study: Landin's Knot for Factorial

Constructs and verifies **Landin's knot** (`landinFact`) in TULIP's semantic model
using **pure higher-order store backpatching** (`Ref (Arr Nat (M Nat))`), with
**zero** syntactic general recursion (`M.recFn`) and **zero** recursive types (`SemTy.mu`)!

Specifically:
1. Allocates a higher-order reference cell `r ← M.new dummyKnotFn` of semantic type
   `ref (Nat → M Nat)` (**0 `▷`s** via `wp_new`).
2. Backpatches `M.set r (knotFactBody r)` (**0 `▷`s** via `wp_set`), where on `d + 1`
   `knotFactBody r` reads `f ← M.get r` (**1 `▷`** via `wp_get_val`) and invokes `f d`.
3. Proves the open higher-order heap invariant `knotInv r` purely via **Löb induction**
   (`bi_loeb_entails`) + `wp_get_val` (1 `▷`) + `wp_bind` + `wp_val`, without unfolding
   the definition of `wpRepaired`!
4. Proves full specification `landinFact_wp` at all stages `n` and worlds `w`:
   `⊤ ⊢ wpRepaired (landinFact x) (BIPred.pureConst (· = fact x))`.
5. Proves general adequacy (`landinFact_adequacy`) AND exact parametric step-counted
   execution (`landinFact_runClosed`: for ALL `x, extra : Nat`, running `landinFact x`
   at stage `x + 1 + extra` on `(∅, ∅)` terminates in `x + 1` guarded heap-read steps
   returning `fact x`, instantiating to `landinFact_run_4 : some (5, 24)`!).
-/

namespace Tulip

/-! ## Derived Sequencing & Continuation Helpers for Program-Logic Proofs -/

/-- Monotonicity of the guarded `▷` modality (`(P ⊢ Q) → (▷ P ⊢ ▷ Q)`). -/
theorem bi_later_mono {n : Nat} {w : World n} {P Q : BIProp n w}
    (hPQ : BIProp.Entails P Q) : BIProp.Entails P.later Q.later := by
  intro m hm w' hw' h hp
  cases m with
  | zero => trivial
  | succ k =>
    exact hPQ k (Nat.le_of_succ_le hm) w'.trunc
      (World.step_le_trans (Nat.le_succ_of_le (Nat.le_refl k)) hm hw' (World.le_refl _))
      (h.restrict (Nat.le_succ_of_le (Nat.le_refl k))) hp

/-- Derived sequencing rule for `M.seq e₁ e₂` from `wp_bind_gen`. -/
theorem wp_seq {n : Nat} {w : World n} {A B : SemTy}
    (e₁ : SemTy.eval n (M A) w) (e₂ : SemTy.eval n (M B) w) (Ψ : BIPred n w B) :
    BIProp.Entails
      (wpRepaired e₁ (BIPred.const A (wpRepaired e₂ Ψ)))
      (wpRepaired (M.seq e₁ e₂) Ψ) := by
  refine wp_bind_gen e₁ (fun _ hm' _ hw'' _ => SemTy.map hw'' (SemTy.restrict hm' e₂))
    (BIPred.const A (wpRepaired e₂ Ψ)) Ψ ?_
  intro m hm w' hw' _ j hj w₂ hw₂ h hp
  dsimp only [BIPred.atVal, BIPred.const] at hp
  have hp' : ((wpRepaired e₂ Ψ).reindex hm hw').holds j hj w₂ hw₂ h := hp
  rw [wpRepaired_reindex] at hp'
  exact hp'

/-- Evaluating `wpBindCont k hnat Ψ` at a concrete value `a` simplifies directly to
`wpRepaired (k a) Ψ`. -/
theorem wpBindCont_app {n : Nat} {w : World n} {A B : SemTy}
    (k : SemTy.eval n (.arr A (M B)) w) (hnat : IsNaturalCont k)
    (Ψ : BIPred n w B) (a : SemTy.eval n A w) :
    (wpBindCont k hnat Ψ).app a =
      wpRepaired (k n (Nat.le_refl n) w (World.restrict_refl_le w) a) Ψ := by
  ext m hm w' hw' h
  dsimp only [BIPred.app, wpBindCont]
  have hk_eq := hnat hm (Nat.le_refl n) (World.restrict_refl_le w) hw' a
  have hrew :
      wpRepaired (k m hm w' hw' (SemTy.map hw' (SemTy.restrict hm a))) (Ψ.reindex hm hw') =
        (wpRepaired (k n (Nat.le_refl n) w (World.restrict_refl_le w) a) Ψ).reindex hm hw' := by
    rw [wpRepaired_reindex, hk_eq]
  constructor
  · intro hp
    rw [hrew] at hp
    exact hp
  · intro hp
    have hp' : ((wpRepaired (k n (Nat.le_refl n) w (World.restrict_refl_le w) a) Ψ).reindex hm hw').holds
        m (Nat.le_refl m) w' (World.restrict_refl_le w') h := hp
    rw [← hrew] at hp'
    exact hp'

/-! ## Mathematical Factorial & Landin's Knot Construction -/

/-- Pure mathematical factorial specification `fact : Nat → Nat`. -/
noncomputable def fact : Nat → Nat
  | 0     => 1
  | d + 1 => (d + 1) * fact d

/-- Semantic type `Nat → M Nat` stored inside the Landin's-knot reference cell. -/
abbrev KnotFn : SemTy := .arr SemTy.nat (M SemTy.nat)

@[simp]
theorem SemTy.map_const {n : Nat} {α : Type 0} {w₁ w₂ : World n}
    (hle : World.Le w₁ w₂) (x : SemTy.eval n (.const α) w₁) :
    SemTy.map (A := .const α) hle x = x := by
  unfold SemTy.map
  rfl

@[simp]
theorem SemTy.restrict_const {m n : Nat} {α : Type 0} {w : World n}
    (hmn : m ≤ n) (x : SemTy.eval n (.const α) w) :
    SemTy.restrict (A := .const α) hmn x = x := by
  unfold SemTy.restrict
  rfl

@[simp]
theorem SemTy.map_prod {n : Nat} {A B : SemTy} {w₁ w₂ : World n}
    (hle : World.Le w₁ w₂) (p : SemTy.eval n (.prod A B) w₁) :
    SemTy.map (A := .prod A B) hle p = (SemTy.map hle p.1, SemTy.map hle p.2) := by
  rcases p with ⟨a, b⟩
  simp [SemTy.map]

@[simp]
theorem SemTy.restrict_prod {m n : Nat} {A B : SemTy} {w : World n}
    (hmn : m ≤ n) (p : SemTy.eval n (.prod A B) w) :
    SemTy.restrict (A := .prod A B) hmn p = (SemTy.restrict hmn p.1, SemTy.restrict hmn p.2) := by
  rcases p with ⟨a, b⟩
  simp [SemTy.restrict]

/-- Dummy initial function `fun _ => ret 0` used to initialize the cell before backpatching. -/
noncomputable def dummyKnotFn {n : Nat} {w : World n} : SemTy.eval n KnotFn w :=
  fun _ _ _ _ _ => M.ret (A := SemTy.nat) (ULift.up 0)

/-- Continuation after reading `f : Nat → M Nat` in the inductive branch `d + 1`:
at runtime store world `(j, w₂, h₂)`, invokes `acc ← f d` and returns `(d + 1) * acc`. -/
noncomputable def knotStepCont {n : Nat} {w : World n} (d : Nat) :
    SemTy.eval n (.arr KnotFn (M SemTy.nat)) w :=
  fun _ _ _ _ f j hj w₂ hw₂ h₂ =>
    M.bind
      (f j hj w₂ hw₂ (ULift.up d))
      (fun _ _ _ _ acc => M.ret (A := SemTy.nat) (ULift.up ((d + 1) * acc.down)))
      j (Nat.le_refl j) w₂ (by simpa using World.le_refl w₂) h₂

theorem knotStepCont_isNatural {n : Nat} {w : World n} (d : Nat) :
    IsNaturalCont (knotStepCont (n := n) (w := w) d) := by
  intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 f
  funext j hj w₃ hw₃ h₃
  simp only [knotStepCont, SemTy.eval_comp_map_restrict, SemTy.eval_arr_map_restrict]

/-- Backpatched open body `knotFactBody r : Nat → M Nat` reading its own cell `r` on
recursive calls (`d + 1`) and taking **zero** `M.recFn` fixed points! -/
noncomputable def knotFactBody {n : Nat} {w : World n}
    (r : SemTy.eval n (.ref KnotFn) w) : SemTy.eval n KnotFn w :=
  fun _ hm _ hw' x =>
    match x.down with
    | 0     => M.ret (A := SemTy.nat) (ULift.up 1)
    | d + 1 =>
        M.bind (M.get (SemTy.map hw' (SemTy.restrict hm r)))
          (knotStepCont d)

@[simp]
theorem knotFactBody_map_restrict {n m : Nat} {w : World n} {w' : World m}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w')
    (r : SemTy.eval n (.ref KnotFn) w) :
    SemTy.map hw' (SemTy.restrict hm (knotFactBody r)) =
      knotFactBody (SemTy.map hw' (SemTy.restrict hm r)) := by
  rcases r with ⟨⟨l, hl⟩⟩
  funext j hj w₂ hw₂ x j' hj' w₃ hw₃ h₃
  simp only [SemTy.eval_arr_map_restrict, knotFactBody]
  cases x.down with
  | zero => rfl
  | succ d =>
    simp only [SemTy.map_restrict_map_restrict]

theorem knotFactBody_isNatural {n : Nat} {w : World n}
    (r : SemTy.eval n (.ref KnotFn) w) :
    IsNaturalCont (knotFactBody r) := by
  rcases r with ⟨⟨l, hl⟩⟩
  intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 x
  funext j hj w₃ hw₃ h₃
  simp only [SemTy.eval_comp_map_restrict, knotFactBody, SemTy.map_const, SemTy.restrict_const]
  cases x.down with
  | zero =>
    simp [M.ret]
  | succ d =>
    simp only [M.bind, knotStepCont]
    have hget_eq :
        M.get (SemTy.map hw₁ (SemTy.restrict hm2 ⟨⟨l, hl⟩⟩)) j (Nat.le_trans hj hm12) w₃
          (World.step_le_trans hj hm12 hw12 hw₃) h₃ =
        M.get (SemTy.map (World.step_le_trans hm12 hm2 hw₁ hw12)
          (SemTy.restrict (Nat.le_trans hm12 hm2) ⟨⟨l, hl⟩⟩)) j hj w₃ hw₃ h₃ := by
      simp only [SemTy.map, SemTy.restrict]
      cases j <;> rfl
    rw [hget_eq]

/-- Top-level call continuation after reading `f ← M.get r`: invokes `f x` at the
runtime store world `(j, w₂, h₂)`. -/
noncomputable def knotInvokeCont {n : Nat} {w : World n} (x : Nat) :
    SemTy.eval n (.arr KnotFn (M SemTy.nat)) w :=
  fun _ _ _ _ f j hj w₂ hw₂ h₂ =>
    f j hj w₂ hw₂ (ULift.up x)
      j (Nat.le_refl j) w₂ (by simpa using World.le_refl w₂) h₂

theorem knotInvokeCont_isNatural {n : Nat} {w : World n} (x : Nat) :
    IsNaturalCont (knotInvokeCont (n := n) (w := w) x) := by
  intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 f
  funext j hj w₃ hw₃ h₃
  simp only [knotInvokeCont, SemTy.eval_comp_map_restrict, SemTy.eval_arr_map_restrict]

/-- **Closed Landin's Knot Factorial Computation (`landinFact x : M Nat`)**:
allocates `r ← new dummyKnotFn`, backpatches `set r (knotFactBody r)`, reads
`f ← get r` out of the heap, and calls `f x`! -/
noncomputable def landinFact {n : Nat} {w : World n} (x : Nat) : SemTy.eval n (M SemTy.nat) w :=
  M.bind (M.new (A := KnotFn) dummyKnotFn) (fun _ _ _ _ r =>
    M.seq (M.set r (knotFactBody r))
      (M.bind (M.get r) (knotInvokeCont x)))

/-! ## Program-Logic Specification via Löb Induction (`bi_loeb_entails`) -/

/-- Precondition `[r ↦ knotFactBody r]` for each call to `knotFactBody r`. -/
noncomputable def knotPre {n : Nat} {w : World n} (r : SemTy.eval n (.ref KnotFn) w) :
    BIPred n w SemTy.nat :=
  BIPred.const SemTy.nat (BIProp.pointsTo r (knotFactBody r))

/-- Postcondition `(input, res) ↦ ([r ↦ knotFactBody r] ∧ res = fact input)`
maintaining the higher-order cell invariant across arbitrarily nested recursive calls! -/
noncomputable def knotPost {n : Nat} {w : World n} (r : SemTy.eval n (.ref KnotFn) w) :
    BIPred n w (.prod SemTy.nat SemTy.nat) where
  holds m hm w' hw' pair h :=
    let r' := SemTy.map hw' (SemTy.restrict hm r)
    (BIProp.pointsTo r' (knotFactBody r')).holds
      m (Nat.le_refl m) w' (World.restrict_refl_le w') h ∧
    pair.2.down = fact pair.1.down
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 pair h₁ h₂ hh ⟨hpt, hfact⟩
    refine ⟨?_, ?_⟩
    · let r₁ := SemTy.map hw₁ (SemTy.restrict hm2 r)
      have hmon : ((BIProp.pointsTo r₁ (knotFactBody r₁)).reindex hm12 hw12).holds
          m₁ (Nat.le_refl m₁) w₂ (World.restrict_refl_le w₂) h₂ :=
        (BIProp.pointsTo r₁ (knotFactBody r₁)).mono hm12 (Nat.le_refl m₂)
          (World.restrict_refl_le w₁) hw12 hh hpt
      have hr_eq := SemTy.map_restrict_map_restrict hm12 hm2 hw₁ hw12 r
      simpa only [BIProp.reindex_pointsTo, knotFactBody_map_restrict, r₁, hr_eq] using hmon
    · simpa using hfact

/-- Open higher-order store invariant for Landin's knot:
`∀ x : Nat, [r ↦ knotFactBody r] -∗ wpRepaired ((knotFactBody r) x) {y. [r ↦ knotFactBody r] ∧ y = fact x}`. -/
noncomputable def knotInv {n : Nat} {w : World n} (r : SemTy.eval n (.ref KnotFn) w) : BIProp n w :=
  BIProp.forallSem
    (wpCallPred (knotFactBody r) (knotFactBody_isNatural r) (knotPre r) (knotPost r))

@[simp]
theorem knotInv_reindex {n m : Nat} {w : World n} {w' : World m}
    (hm : m ≤ n) (hw' : World.Le (w.restrict hm) w')
    (r : SemTy.eval n (.ref KnotFn) w) :
    (knotInv r).reindex hm hw' = knotInv (SemTy.map hw' (SemTy.restrict hm r)) := by
  ext j hj w₂ hw₂ h
  dsimp only [BIProp.reindex, knotInv, BIProp.forallSem]
  have haux : ∀ (j' : Nat) (hj' : j' ≤ j) (w₃ : World j')
      (hw₃ : World.Le (w₂.restrict hj') w₃) (a : SemTy.eval j' SemTy.nat w₃),
      (wpCallPred (knotFactBody r) (knotFactBody_isNatural r) (knotPre r) (knotPost r)).holds
        j' (Nat.le_trans hj' (Nat.le_trans hj hm)) w₃
        (World.step_le_trans hj' (Nat.le_trans hj hm) (World.step_le_trans hj hm hw' hw₂) hw₃) a =
      (wpCallPred (knotFactBody (SemTy.map hw' (SemTy.restrict hm r)))
        (knotFactBody_isNatural (SemTy.map hw' (SemTy.restrict hm r)))
        (knotPre (SemTy.map hw' (SemTy.restrict hm r)))
        (knotPost (SemTy.map hw' (SemTy.restrict hm r)))).holds
        j' (Nat.le_trans hj' hj) w₃ (World.step_le_trans hj' hj hw₂ hw₃) a := by
    intro j' hj' w₃ hw₃ a
    funext h₃
    dsimp only [wpCallPred]
    have hpre_eq : (knotPre r).atVal (Nat.le_trans hj' (Nat.le_trans hj hm))
        (World.step_le_trans hj' (Nat.le_trans hj hm) (World.step_le_trans hj hm hw' hw₂) hw₃) a =
        (knotPre (SemTy.map hw' (SemTy.restrict hm r))).atVal (Nat.le_trans hj' hj)
          (World.step_le_trans hj' hj hw₂ hw₃) a := by
      ext q hq w₄ hw₄ h₄
      simp only [BIPred.atVal, knotPre, BIPred.const, BIProp.pointsTo,
        SemTy.map_ref_val, SemTy.restrict_ref_val, knotFactBody_map_restrict,
        SemTy.map_restrict_map_restrict]
    have hpost_eq : (knotPost r).curry (Nat.le_trans hj' (Nat.le_trans hj hm))
        (World.step_le_trans hj' (Nat.le_trans hj hm) (World.step_le_trans hj hm hw' hw₂) hw₃) a =
        (knotPost (SemTy.map hw' (SemTy.restrict hm r))).curry (Nat.le_trans hj' hj)
          (World.step_le_trans hj' hj hw₂ hw₃) a := by
      ext q hq w₄ hw₄ b h₄
      simp only [BIPred.curry, knotPost, BIProp.pointsTo,
        SemTy.map_ref_val, SemTy.restrict_ref_val, knotFactBody_map_restrict,
        SemTy.map_restrict_map_restrict]
    have hfn_eq : knotFactBody r j' (Nat.le_trans hj' (Nat.le_trans hj hm)) w₃
        (World.step_le_trans hj' (Nat.le_trans hj hm) (World.step_le_trans hj hm hw' hw₂) hw₃) a =
        knotFactBody (SemTy.map hw' (SemTy.restrict hm r)) j' (Nat.le_trans hj' hj) w₃
          (World.step_le_trans hj' hj hw₂ hw₃) a := by
      have hmr := knotFactBody_map_restrict hm hw' r
      have happ := congrFun (congrFun (congrFun (congrFun (congrFun hmr j') (Nat.le_trans hj' hj))
        w₃) (World.step_le_trans hj' hj hw₂ hw₃)) a
      rw [← happ, SemTy.eval_arr_map_restrict]
    rw [hpre_eq, hpost_eq, hfn_eq]
  constructor <;> intro hall j' hj' w₃ hw₃ h₃ a hh₃
  · rw [← haux j' hj' w₃ hw₃ a]; exact hall j' hj' w₃ hw₃ h₃ a hh₃
  · rw [haux j' hj' w₃ hw₃ a]; exact hall j' hj' w₃ hw₃ h₃ a hh₃

/-- Applying `knotStepCont d` to `knotFactBody r` equals `M.bind (knotFactBody r d) (...)`
because `knotFactBody r` is natural! -/
theorem knotStepCont_knotFactBody {n : Nat} {w : World n}
    (r : SemTy.eval n (.ref KnotFn) w) (d : Nat) :
    knotStepCont d n (Nat.le_refl n) w (World.restrict_refl_le w) (knotFactBody r) =
      M.bind
        (knotFactBody r n (Nat.le_refl n) w (World.restrict_refl_le w) (ULift.up d))
        (fun _ _ _ _ acc => M.ret (A := SemTy.nat) (ULift.up ((d + 1) * acc.down))) := by
  funext j hj w₂ hw₂ h₂
  dsimp only [knotStepCont]
  have hn := knotFactBody_isNatural r hj (Nat.le_refl n) (World.restrict_refl_le w) hw₂ (ULift.up d)
  simp only [SemTy.map_const, SemTy.restrict_const] at hn
  rw [← hn]
  simp only [M.bind, M.ret, SemTy.eval_comp_map_restrict]

/-- Applying `knotInvokeCont x` to `knotFactBody r` equals `knotFactBody r x`. -/
theorem knotInvokeCont_knotFactBody {n : Nat} {w : World n}
    (r : SemTy.eval n (.ref KnotFn) w) (x : Nat) :
    knotInvokeCont x n (Nat.le_refl n) w (World.restrict_refl_le w) (knotFactBody r) =
      knotFactBody r n (Nat.le_refl n) w (World.restrict_refl_le w) (ULift.up x) := by
  funext j hj w₂ hw₂ h₂
  dsimp only [knotInvokeCont]
  have hn := knotFactBody_isNatural r hj (Nat.le_refl n) (World.restrict_refl_le w) hw₂ (ULift.up x)
  simp only [SemTy.map_const, SemTy.restrict_const] at hn
  rw [← hn, SemTy.eval_comp_map_restrict]

/-- Core single-step lemma for Landin's knot: under `▷ (knotInv r)`, owning
`[r ↦ knotFactBody r]` suffices to verify `knotFactBody r x`!
Proved **100% via the program-logic rules** (`wp_val`, `wp_get_val`, `wp_bind`,
`wp_bind_gen`, `bi_later_mono`, `bi_sep_comm`, `bi_sep_top`, `bi_wand_adj`) —
zero `wpRepaired` unfolding! -/
theorem knotFactBody_step {n : Nat} {w : World n}
    (r : SemTy.eval n (.ref KnotFn) w) (x : SemTy.eval n SemTy.nat w) :
    BIProp.Entails
      ((knotInv r).later.sep (BIProp.pointsTo r (knotFactBody r)))
      (wpRepaired
        (knotFactBody r n (Nat.le_refl n) w (by simpa using World.le_refl w) x)
        ((knotPost r).curry (Nat.le_refl n) (World.restrict_refl_le w) x)) := by
  let Post_x := (knotPost r).curry (Nat.le_refl n) (World.restrict_refl_le w) x
  dsimp only [knotFactBody]
  cases hx : x.down with
  | zero =>
    have hdrop : BIProp.Entails
        ((knotInv r).later.sep (BIProp.pointsTo r (knotFactBody r)))
        (BIProp.pointsTo r (knotFactBody r)) := by
      rintro m hm w' hw' h ⟨h₁, h₂, hd, rfl, _, hpt⟩
      rw [ParHeap.union_comm hd]
      exact (BIProp.pointsTo r (knotFactBody r)).mono_heap hm hw' ⟨h₁, hd.symm, rfl⟩ hpt
    refine BIProp.entails_trans hdrop
      (BIProp.entails_trans ?_ (wp_val (A := SemTy.nat) (ULift.up 1) Post_x))
    intro m hm w' hw' h hpt
    dsimp only [BIPred.app, Post_x, BIPred.curry, knotPost]
    refine ⟨?_, by simp [hx, fact]⟩
    have hpt' : ((BIProp.pointsTo r (knotFactBody r)).reindex hm hw').holds
        m (Nat.le_refl m) w' (World.restrict_refl_le w') h := hpt
    simpa only [BIProp.reindex_pointsTo, knotFactBody_map_restrict] using hpt'
  | succ d =>
    have hr_refl : SemTy.map (by simpa using World.le_refl w) (SemTy.restrict (Nat.le_refl n) r) = r :=
      SemTy.restrict_refl_map (World.restrict_refl_le w) r
    rw [hr_refl]
    let Φ_get := wpBindCont (knotStepCont d) (knotStepCont_isNatural d) Post_x
    refine BIProp.entails_trans ?_
      (wp_bind (M.get r) (knotStepCont d) (knotStepCont_isNatural d) Post_x)
    rw [bi_sep_comm]
    refine BIProp.entails_trans
      (bi_sep_mono (BIProp.entails_refl _) ?_)
      (wp_get_val r (knotFactBody r) Φ_get)
    apply bi_later_mono
    rw [wpBindCont_app (knotStepCont d) (knotStepCont_isNatural d) Post_x (knotFactBody r),
      knotStepCont_knotFactBody]
    apply (bi_wand_adj _ _ _).mp
    rintro m hm w' hw' h ⟨h₁, h₂, hd12, rfl, hinv, hpt⟩
    have hinv_inst := hinv m (Nat.le_refl m) w' (World.restrict_refl_le w') h₁ (ULift.up d)
      (by rw [ParHeap.restrict_refl_map]; exact ParHeap.le_refl h₁)
    dsimp only [wpCallPred, BIProp.wand] at hinv_inst
    have h₁_refl : (h₁.restrict (Nat.le_refl m)).map (World.restrict_refl_le w') = h₁ :=
      ParHeap.restrict_refl_map h₁
    have hwp_d := hinv_inst m (Nat.le_refl m) w' (World.restrict_refl_le w') h₂
      (by rw [h₁_refl]; exact hd12) hpt
    rw [h₁_refl] at hwp_d
    have hgoal_eq :
        ((wpRepaired
          (M.bind (knotFactBody r n (Nat.le_refl n) w (World.restrict_refl_le w) (ULift.up d))
            (fun _ _ _ _ acc => M.ret (A := SemTy.nat) (ULift.up ((d + 1) * acc.down))))
          Post_x).reindex hm hw').holds m (Nat.le_refl m) w' (World.restrict_refl_le w')
          (h₁.union h₂) →
        (wpRepaired
          (M.bind (knotFactBody r n (Nat.le_refl n) w (World.restrict_refl_le w) (ULift.up d))
            (fun _ _ _ _ acc => M.ret (A := SemTy.nat) (ULift.up ((d + 1) * acc.down))))
          Post_x).holds m hm w' hw' (h₁.union h₂) := id
    apply hgoal_eq
    rw [wpRepaired_reindex]
    have hbind_restr :
        SemTy.map hw' (SemTy.restrict hm
          (M.bind (knotFactBody r n (Nat.le_refl n) w (World.restrict_refl_le w) (ULift.up d))
            (fun _ _ _ _ acc => M.ret (A := SemTy.nat) (ULift.up ((d + 1) * acc.down))))) =
        M.bind (knotFactBody r m hm w' hw' (ULift.up d))
          (fun _ _ _ _ acc => M.ret (A := SemTy.nat) (ULift.up ((d + 1) * acc.down))) := by
      have hn := knotFactBody_isNatural r hm (Nat.le_refl n) (World.restrict_refl_le w) hw' (ULift.up d)
      simp only [SemTy.map_const, SemTy.restrict_const] at hn
      funext j hj w₂ hw₂ h₂
      rw [← hn]
      simp only [M.bind, M.ret, SemTy.eval_comp_map_restrict]
    rw [hbind_restr]
    refine wp_bind_gen
      (knotFactBody r m hm w' hw' (ULift.up d))
      (fun _ _ _ _ acc => M.ret (A := SemTy.nat) (ULift.up ((d + 1) * acc.down)))
      ((knotPost r).curry hm hw' (ULift.up d))
      (Post_x.reindex hm hw')
      ?_ m (Nat.le_refl m) w' (World.restrict_refl_le w') (h₁.union h₂) hwp_d
    intro j hj w₂ hw₂ acc
    refine BIProp.entails_trans ?_
      (wp_val (A := SemTy.nat) (ULift.up ((d + 1) * acc.down))
        ((Post_x.reindex hm hw').reindex hj hw₂))
    rintro q hq w₃ hw₃ h₃ ⟨hpt_q, hacc_eq⟩
    dsimp only [BIPred.app, BIPred.reindex, Post_x, BIPred.curry, knotPost] at hpt_q ⊢
    refine ⟨?_, ?_⟩
    · simpa only [BIProp.pointsTo, SemTy.map_ref_val, SemTy.restrict_ref_val,
        knotFactBody_map_restrict, SemTy.map_restrict_map_restrict] using hpt_q
    · simp only [SemTy.map_const, SemTy.restrict_const] at hacc_eq ⊢
      simp [hx, fact, hacc_eq]

/-- **Löb-Inductive Proof of `knotInv r`**:
`⊤ ⊢ ∀ x, [r ↦ knotFactBody r] -∗ wpRepaired ((knotFactBody r) x) {y. [r ↦ knotFactBody r] ∧ y = fact x}`! -/
theorem knotInv_holds {n : Nat} {w : World n} (r : SemTy.eval n (.ref KnotFn) w) :
    BIProp.Entails (BIProp.top n w) (knotInv r) := by
  apply bi_loeb_entails
  rintro m hm w₀ hw₀ h ⟨_, hlat⟩
  intro j hj w₁ hw₁ h₁ x hh₁
  let r₁ := SemTy.map (World.step_le_trans hj hm hw₀ hw₁) (SemTy.restrict (Nat.le_trans hj hm) r)
  have hlat₁ : (knotInv r₁).later.holds j (Nat.le_refl j) w₁ (World.restrict_refl_le w₁) h₁ := by
    have hm_lat : ((knotInv r).later.reindex (Nat.le_trans hj hm)
        (World.step_le_trans hj hm hw₀ hw₁)).holds
        j (Nat.le_refl j) w₁ (World.restrict_refl_le w₁) h₁ :=
      (knotInv r).later.mono hj hm hw₀ hw₁ hh₁ hlat
    simpa only [BIProp.reindex_later, knotInv_reindex] using hm_lat
  have hwand := ((bi_wand_adj
      (knotInv r₁).later
      (BIProp.pointsTo r₁ (knotFactBody r₁))
      (wpRepaired (knotFactBody r₁ j (Nat.le_refl j) w₁ (by simpa using World.le_refl w₁) x)
        ((knotPost r₁).curry (Nat.le_refl j) (World.restrict_refl_le w₁) x))).mp
      (knotFactBody_step r₁ x))
    j (Nat.le_refl j) w₁ (World.restrict_refl_le w₁) h₁ hlat₁
  dsimp only [wpCallPred]
  have hpre_eq : (knotPre r).atVal (Nat.le_trans hj hm) (World.step_le_trans hj hm hw₀ hw₁) x =
      BIProp.pointsTo r₁ (knotFactBody r₁) := by
    ext q hq w₂ hw₂ h₂
    simp only [BIPred.atVal, knotPre, BIPred.const, BIProp.pointsTo, r₁,
      SemTy.map_ref_val, SemTy.restrict_ref_val, knotFactBody_map_restrict,
      SemTy.map_restrict_map_restrict]
  have hpost_eq : (knotPost r).curry (Nat.le_trans hj hm) (World.step_le_trans hj hm hw₀ hw₁) x =
      (knotPost r₁).curry (Nat.le_refl j) (World.restrict_refl_le w₁) x := by
    ext q hq w₂ hw₂ b h₂
    simp only [BIPred.curry, knotPost, BIProp.pointsTo, r₁,
      SemTy.map_ref_val, SemTy.restrict_ref_val, knotFactBody_map_restrict,
      SemTy.map_restrict_map_restrict]
  have hfn_eq : knotFactBody r j (Nat.le_trans hj hm) w₁ (World.step_le_trans hj hm hw₀ hw₁) x =
      knotFactBody r₁ j (Nat.le_refl j) w₁ (by simpa using World.le_refl w₁) x := by
    have hmr := knotFactBody_map_restrict (Nat.le_trans hj hm) (World.step_le_trans hj hm hw₀ hw₁) r
    have happ := congrFun (congrFun (congrFun (congrFun (congrFun hmr j) (Nat.le_refl j))
      w₁) (by simpa using World.le_refl w₁)) x
    rw [← happ, SemTy.eval_arr_map_restrict]
  rw [hpre_eq, hpost_eq, hfn_eq]
  exact hwand

/-- **Full Program-Logic Specification of Landin's Knot (`landinFact_wp`)**:
At EVERY stage `n`, world `w`, and input `x : Nat`:
`⊤ ⊢ wpRepaired (landinFact x) (BIPred.pureConst (· = fact x))`!
Uses `wp_new` (**0 `▷`s**) + `wp_set` (**0 `▷`s**) + `wp_get_val` (**1 `▷`**) + `knotInv_holds` (`bi_loeb`)! -/
theorem landinFact_wp (n : Nat) (w : World n) (x : Nat) :
    BIProp.Entails (BIProp.top n w)
      (wpRepaired (landinFact (n := n) (w := w) x) (BIPred.pureConst (· = fact x))) := by
  let PostPure : BIPred n w SemTy.nat := BIPred.pureConst (· = fact x)
  let AllocCont : SemTy.eval n (.arr (.ref KnotFn) (M SemTy.nat)) w :=
    fun _ _ _ _ r =>
      M.seq (M.set r (knotFactBody r))
        (M.bind (M.get r) (knotInvokeCont x))
  have hAlloc_nat : IsNaturalCont AllocCont := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 r
    rcases r with ⟨⟨l, hl⟩⟩
    funext j hj w₃ hw₃ h₃
    simp only [AllocCont, M.seq, M.bind, M.set, knotInvokeCont,
      SemTy.eval_comp_map_restrict, knotFactBody_map_restrict, StepLift.bind_ret,
      SemTy.map_restrict_map_restrict, SemTy.map_ref_val, SemTy.restrict_ref_val]
    have hget_eq :
        M.get (⟨⟨l, hl⟩⟩ : SemTy.eval m₂ (.ref KnotFn) w₁) j (Nat.le_trans hj hm12) w₃
          (World.step_le_trans hj hm12 hw12 hw₃) =
        M.get (SemTy.map hw12 (SemTy.restrict hm12 (⟨⟨l, hl⟩⟩ : SemTy.eval m₂ (.ref KnotFn) w₁)))
          j hj w₃ hw₃ := by
      funext h_in
      simp only [SemTy.map, SemTy.restrict]
      cases j <;> rfl
    congr 1
    congr 1
    rw [hget_eq]
  refine BIProp.entails_trans ?_
    (wp_bind (M.new (A := KnotFn) dummyKnotFn) AllocCont hAlloc_nat PostPure)
  refine BIProp.entails_trans ?_
    (wp_new dummyKnotFn (wpBindCont AllocCont hAlloc_nat PostPure))
  intro m hm w₀ hw₀ h _ j hj w₁ hw₁ h₁ r _
  dsimp only [wpNewPre]
  refine ((bi_wand_adj (BIProp.top j w₁)
    (BIProp.pointsTo r (SemTy.map (World.step_le_trans hj hm hw₀ hw₁)
      (SemTy.restrict (Nat.le_trans hj hm) dummyKnotFn)))
    ((wpBindCont AllocCont hAlloc_nat PostPure).atVal (Nat.le_trans hj hm)
      (World.step_le_trans hj hm hw₀ hw₁) r)).mp ?_)
    j (Nat.le_refl j) w₁ (World.restrict_refl_le w₁) h₁ trivial
  rintro q hq w₂ hw₂ h₂ ⟨h_emp, h_r, hd_er, rfl, _, hpt_dummy⟩
  let r₂ := SemTy.map hw₂ (SemTy.restrict hq r)
  let GoalPure : BIPred q w₂ SemTy.nat := BIPred.pureConst (· = fact x)
  have hgoal_conv :
      (wpRepaired (AllocCont q (Nat.le_trans hq (Nat.le_trans hj hm)) w₂
          (World.step_le_trans hq (Nat.le_trans hj hm) (World.step_le_trans hj hm hw₀ hw₁) hw₂) r₂)
        GoalPure).holds q (Nat.le_refl q) w₂ (World.restrict_refl_le w₂) (h_emp.union h_r) →
      ((wpBindCont AllocCont hAlloc_nat PostPure).atVal (Nat.le_trans hj hm)
        (World.step_le_trans hj hm hw₀ hw₁) r).holds q hq w₂ hw₂ (h_emp.union h_r) := by
    intro hwp_q
    dsimp only [BIPred.atVal, wpBindCont]
    exact hwp_q
  apply hgoal_conv
  dsimp only [AllocCont]
  refine wp_seq (M.set r₂ (knotFactBody r₂))
    (M.bind (M.get r₂) (knotInvokeCont x)) GoalPure
    q (Nat.le_refl q) w₂ (World.restrict_refl_le w₂) (h_emp.union h_r) ?_
  refine wp_set r₂ (knotFactBody r₂)
    (BIPred.const SemTy.unit (wpRepaired (M.bind (M.get r₂) (knotInvokeCont x)) GoalPure))
    q (Nat.le_refl q) w₂ (World.restrict_refl_le w₂) (h_emp.union h_r) ?_
  refine ⟨h_r, h_emp, hd_er.symm, ParHeap.union_comm hd_er, ?_, ?_⟩
  · refine ⟨SemTy.map hw₂ (SemTy.restrict hq (SemTy.map (World.step_le_trans hj hm hw₀ hw₁)
      (SemTy.restrict (Nat.le_trans hj hm) dummyKnotFn))), ?_⟩
    dsimp only [BIProp.pointsTo] at hpt_dummy
    dsimp only [pointsToAnyPred]
    have hloc_eq : r₂.down.1 = r.down.1 := by
      simp [r₂, SemTy.map_ref_val, SemTy.restrict_ref_val]
    have hsing_eq : ∀ {l₁ l₂ : Loc} (heq : l₁ = l₂)
        (hl₁ : w₂.cells l₁ = some (SemTy.nextAt q KnotFn))
        (hl₂ : w₂.cells l₂ = some (SemTy.nextAt q KnotFn)),
        ParHeap.singleton l₁ hl₁
          (SemTy.map hw₂ (SemTy.restrict hq (SemTy.map (World.step_le_trans hj hm hw₀ hw₁)
            (SemTy.restrict (Nat.le_trans hj hm) dummyKnotFn)))) =
        ParHeap.singleton l₂ hl₂
          (SemTy.map hw₂ (SemTy.restrict hq (SemTy.map (World.step_le_trans hj hm hw₀ hw₁)
            (SemTy.restrict (Nat.le_trans hj hm) dummyKnotFn)))) := by
      rintro _ _ rfl _ _
      rfl
    rw [hsing_eq hloc_eq]
    exact hpt_dummy
  · refine ((bi_wand_adj (BIProp.top q w₂) (BIProp.pointsTo r₂ (knotFactBody r₂))
      (wpRepaired (M.bind (M.get r₂) (knotInvokeCont x)) GoalPure)).mp ?_)
      q (Nat.le_refl q) w₂ (World.restrict_refl_le w₂) h_emp trivial
    let Φ_top := wpBindCont (knotInvokeCont x) (knotInvokeCont_isNatural x) GoalPure
    refine BIProp.entails_trans ?_
      (wp_bind (M.get r₂) (knotInvokeCont x) (knotInvokeCont_isNatural x) GoalPure)
    rw [bi_sep_comm]
    refine BIProp.entails_trans
      (bi_sep_mono (BIProp.entails_refl _) ?_)
      (wp_get_val r₂ (knotFactBody r₂) Φ_top)
    refine BIProp.entails_trans (bi_later_intro _) (bi_later_mono ?_)
    rw [wpBindCont_app (knotInvokeCont x) (knotInvokeCont_isNatural x) GoalPure (knotFactBody r₂),
      knotInvokeCont_knotFactBody]
    apply (bi_wand_adj _ _ _).mp
    rintro p hp w₃ hw₃ h₃ ⟨h_t, h_pt, hd_tp, rfl, _, hpt₃⟩
    let r₃ := SemTy.map hw₃ (SemTy.restrict hp r₂)
    have hinv₃ := knotInv_holds r₃ p (Nat.le_refl p) w₃ (World.restrict_refl_le w₃)
      h_t trivial p (Nat.le_refl p) w₃ (World.restrict_refl_le w₃) h_t (ULift.up x)
      (by rw [ParHeap.restrict_refl_map]; exact ParHeap.le_refl h_t)
    dsimp only [wpCallPred, BIProp.wand] at hinv₃
    have ht_refl : (h_t.restrict (Nat.le_refl p)).map (World.restrict_refl_le w₃) = h_t :=
      ParHeap.restrict_refl_map h_t
    have hpt₃' : ((knotPre r₃).atVal (Nat.le_refl p) (World.restrict_refl_le w₃) (ULift.up x)).holds
        p (Nat.le_refl p) w₃ (World.restrict_refl_le w₃) h_pt := by
      simpa only [BIPred.atVal, knotPre, BIPred.const, BIProp.pointsTo, r₃,
        SemTy.map_ref_val, SemTy.restrict_ref_val, knotFactBody_map_restrict,
        SemTy.restrict_refl_map] using hpt₃
    have hwp_call := hinv₃ p (Nat.le_refl p) w₃ (World.restrict_refl_le w₃) h_pt
      (by rw [ht_refl]; exact hd_tp) hpt₃'
    rw [ht_refl] at hwp_call
    have hmono := wp_mono
      (knotFactBody r₃ p (Nat.le_refl p) w₃ (by simpa using World.le_refl w₃) (ULift.up x))
      (Ψ := GoalPure.reindex hp hw₃)
      (fun j' hj' w₄ hw₄ _ _ hp_post => by
        dsimp only [BIPred.reindex, GoalPure, BIPred.pureConst]
        have hd_eq : (SemTy.map (A := SemTy.nat) hw₄
            (SemTy.restrict (A := SemTy.nat) hj' (ULift.up x : SemTy.eval p SemTy.nat w₃))).down = x := by
          simp [SemTy.nat, SemTy.map_const, SemTy.restrict_const]
        have hp2 := hp_post.2
        rw [hd_eq] at hp2
        exact hp2)
      p (Nat.le_refl p) w₃ (World.restrict_refl_le w₃) (h_t.union h_pt) hwp_call
    have hbody_eq :
        knotFactBody r₃ p (Nat.le_refl p) w₃ (by simpa using World.le_refl w₃) (ULift.up x) =
        SemTy.map hw₃ (SemTy.restrict hp
          (knotFactBody r₂ q (Nat.le_refl q) w₂ (World.restrict_refl_le w₂) (ULift.up x))) := by
      have hn := knotFactBody_isNatural r₂ hp (Nat.le_refl q) (World.restrict_refl_le w₂) hw₃ (ULift.up x)
      have hx_eq : SemTy.map (A := SemTy.nat) hw₃
          (SemTy.restrict (A := SemTy.nat) hp (ULift.up x : SemTy.eval q SemTy.nat w₂)) = ULift.up x := by
        simp [SemTy.nat, SemTy.map_const, SemTy.restrict_const]
      rw [hx_eq] at hn
      rw [hn]
      have hmr := knotFactBody_map_restrict hp hw₃ r₂
      have happ := congrFun (congrFun (congrFun (congrFun (congrFun hmr p) (Nat.le_refl p))
        w₃) (by simpa using World.le_refl w₃)) (ULift.up x)
      rw [← happ, SemTy.eval_arr_map_restrict]
    rw [hbody_eq, ← wpRepaired_reindex] at hmono
    exact hmono

/-! ## Closed Adequacy & Parametric Step-Counted Execution of Landin's Knot -/

/-- **General Closed Adequacy of Landin's Knot (`landinFact_adequacy`)**:
For ANY `x, k : Nat`, if `landinFact x` run on `(∅, ∅)` at stage `k + 1` terminates
in `≤ k` steps returning `v : Nat`, then `v = fact x`! -/
theorem landinFact_adequacy (k x : Nat)
    {j : Nat} {hj : j ≤ k + 1}
    {ans : CompAns SemTy.nat (k + 1) (World.empty (k + 1)) j hj}
    {v : Nat}
    (hterm : StepLift.TerminatesWith
      (landinFact (n := k + 1) (w := World.empty (k + 1)) x
        (k + 1) (Nat.le_refl (k + 1)) (World.empty (k + 1))
        (by simpa using World.le_refl (World.empty (k + 1)))
        (Heaplet.empty (World.empty (k + 1))))
      k j hj ans)
    (hval : ans.2.2.2 = ULift.up v) :
    v = fact x :=
  wp_adequacy (P := (· = fact x)) (landinFact x)
    (landinFact_wp (k + 1) (World.empty (k + 1)) x) hterm hval

@[simp]
theorem StepLift.extractBy_map {α : Type 0} :
    ∀ {n : Nat} {X Y : (m : Nat) → m ≤ n → Type 1}
      (proj : ∀ (m : Nat) (hm : m ≤ n), Y m hm → α)
      (f : ∀ (m : Nat) (hm : m ≤ n), X m hm → Y m hm)
      (c : StepLift n X),
      StepLift.extractBy proj (StepLift.map f c) =
        StepLift.extractBy (fun m hm x => proj m hm (f m hm x)) c
  | 0,     _, _, _,    _, Sum.inl _  => rfl
  | 0,     _, _, _,    _, Sum.inr _  => rfl
  | _ + 1, _, _, _,    _, Sum.inl _  => rfl
  | _ + 1, _, _, proj, f, Sum.inr c' => by
      dsimp only [StepLift.map, StepLift.extractBy]
      rw [StepLift.extractBy_map]

theorem StepLift.extractBy_post {α β : Type 0} :
    ∀ {n : Nat} {X : (m : Nat) → m ≤ n → Type 1}
      (proj : ∀ (m : Nat) (hm : m ≤ n), X m hm → α)
      (g : α → β)
      (c : StepLift n X),
      StepLift.extractBy (fun m hm x => g (proj m hm x)) c =
        (StepLift.extractBy proj c).map (fun sv => (sv.1, g sv.2))
  | 0,     _, _,    _, Sum.inl _  => rfl
  | 0,     _, _,    _, Sum.inr _  => rfl
  | _ + 1, _, _,    _, Sum.inl _  => rfl
  | _ + 1, _, proj, g, Sum.inr c' => by
      dsimp only [StepLift.extractBy]
      rw [StepLift.extractBy_post (fun j hj x => proj j (Nat.le_succ_of_le hj) x) g c']
      cases StepLift.extractBy (fun j hj x => proj j (Nat.le_succ_of_le hj) x) c' <;> rfl

theorem StepLift.bind_ret_post {n : Nat} {X Y : (m : Nat) → m ≤ n → Type 1}
    (c : StepLift n X)
    (g : ∀ (m : Nat) (hm : m ≤ n), X m hm → Y m hm) :
    StepLift.bind c (fun m hm x =>
        StepLift.ret (n := m) (X := fun j hj => Y j (Nat.le_trans hj hm)) (g m hm x)) =
      StepLift.map g c := by
  induction n with
  | zero => cases c <;> rfl
  | succ k ih =>
    cases c with
    | inl _ => rfl
    | inr c' => exact congrArg Sum.inr (ih c' _)

theorem World.trunc_cells_nextAt (q : Nat) (w : World (q + 1)) (l : Loc) (A : SemTy)
    (hl : w.cells l = some A) :
    w.trunc.cells l = some (SemTy.nextAt q A) := by
  cases q <;> simp [World.trunc, World.restrict_cells, SemTy.nextAt, LaterTy.restrict, hl]

/-- Exact step-counted symbolic evaluation of `knotFactBody r x` on any store where
cell `l` holds `knotFactBody r`: takes `x` guarded `get` steps and returns `fact x`! -/
theorem knotFactBody_extract :
    ∀ (x m : Nat) (_ : x ≤ m) (w' : World m) (l : Loc)
      (hl' : w'.cells l = some (SemTy.nextAt m KnotFn))
      (h₀ : TotHeap m w'),
      StepLift.extractBy (fun _ _ ans => ans.2.2.2.down)
        (knotFactBody (n := m) (w := w') ⟨⟨l, hl'⟩⟩
          m (Nat.le_refl m) w' (by simpa using World.le_refl w') (ULift.up x)
          m (Nat.le_refl m) w' (by simpa using World.le_refl w')
          (TotHeap.update (A := KnotFn) h₀ l hl'
            (CellVal.nextVal (knotFactBody (n := m) (w := w') ⟨⟨l, hl'⟩⟩)))) =
      some (x, fact x)
  | 0, m, _, w', l, hl', h₀ => by
      simp only [knotFactBody, M.ret]
      cases m <;> simp [StepLift.ret, StepLift.extractBy, fact]
  | d + 1, 0, hdm, _, _, _, _ => nomatch hdm
  | d + 1, q + 1, hdm, w', l, hl', h₀ => by
      have hdq : d ≤ q := Nat.le_of_succ_le_succ hdm
      let hk_le : q ≤ q + 1 := Nat.le_succ_of_le (Nat.le_refl q)
      have hl_q1 : w'.cells l = some KnotFn := hl'
      have hl_tr : w'.trunc.cells l = some (SemTy.nextAt q KnotFn) :=
        World.trunc_cells_nextAt q w' l KnotFn hl_q1
      let r_q1 : SemTy.eval (q + 1) (.ref KnotFn) w' := ⟨⟨l, hl_q1⟩⟩
      let r_q : SemTy.eval q (.ref KnotFn) w'.trunc := ⟨⟨l, hl_tr⟩⟩
      have hr_q_eq : SemTy.map (World.le_refl w'.trunc) (SemTy.restrict hk_le r_q1) = r_q := by
        simp [r_q1, r_q, SemTy.restrict]
      have hget_val :
          CellVal.toEval ((TotHeap.update (A := KnotFn) h₀ l hl_q1
            (CellVal.nextVal (knotFactBody r_q1))).get l KnotFn hl_q1) =
          knotFactBody r_q := by
        change CellVal.toEval ((TotHeap.update (A := KnotFn) h₀ l hl_q1
          (CellVal.nextVal (knotFactBody r_q1))).get l (SemTy.nextAt (q + 1) KnotFn) hl_q1) =
          knotFactBody r_q
        rw [TotHeap.update_same (A := KnotFn) h₀ l hl_q1 (CellVal.nextVal (knotFactBody r_q1))]
        dsimp only [CellVal.nextVal]
        rw [CellVal.toEval_ofEval]
        have hmr := knotFactBody_map_restrict hk_le (World.le_refl w'.trunc) r_q1
        rw [SemTy.map_refl, hr_q_eq] at hmr
        exact hmr
      have htrunc_upd :
          TotHeap.trunc (TotHeap.update (A := KnotFn) h₀ l hl_q1
            (CellVal.nextVal (knotFactBody r_q1))) =
          TotHeap.update (A := KnotFn) (TotHeap.trunc h₀) l hl_tr
            (CellVal.nextVal (knotFactBody r_q)) := by
        rw [TotHeap.trunc_update]
        have hmr := knotFactBody_map_restrict hk_le (World.le_refl w'.trunc) r_q1
        rw [SemTy.map_refl, hr_q_eq] at hmr
        rw [hmr]
      dsimp only [knotFactBody]
      simp only [M.bind, M.get, SemTy.map, SemTy.restrict,
        StepLift.bind_stepSucc, StepLift.bind_ret]
      dsimp only [StepLift.stepSucc, StepLift.extractBy]
      rw [StepLift.extractBy_map]
      dsimp only [knotStepCont, M.reanchorAns]
      rw [hget_val, htrunc_upd]
      have hpost_bind :
          M.bind (A := SemTy.nat) (B := SemTy.nat)
            (knotFactBody r_q q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
              (ULift.up d))
            (fun _ _ _ _ acc => M.ret (A := SemTy.nat) (ULift.up ((d + 1) * acc.down)))
            q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
            (TotHeap.update (A := KnotFn) (TotHeap.trunc h₀) l hl_tr
              (CellVal.nextVal (knotFactBody r_q))) =
          StepLift.map
            (fun j hj ans =>
              M.reanchorAns (A := SemTy.nat) hj ans.2.1.proof j (Nat.le_refl j)
                ⟨ans.1, ⟨by simpa using World.le_refl ans.1⟩, ans.2.2.1,
                  (ULift.up ((d + 1) * ans.2.2.2.down) : SemTy.eval j SemTy.nat ans.1)⟩)
            (knotFactBody r_q q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
              (ULift.up d) q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
              (TotHeap.update (A := KnotFn) (TotHeap.trunc h₀) l hl_tr
                (CellVal.nextVal (knotFactBody r_q)))) := by
        dsimp only [M.bind, M.ret]
        have hcont : ∀ (j : Nat) (hj : j ≤ q) (ans : CompAns SemTy.nat q w'.trunc j hj),
            StepLift.map (M.reanchorAns (A := SemTy.nat) hj ans.2.1.proof)
              (StepLift.ret (X := CompAns SemTy.nat j ans.1)
                ⟨ans.1, ⟨by simpa using World.le_refl ans.1⟩, ans.2.2.1,
                  SemTy.map (A := SemTy.nat) (by simpa using World.le_refl ans.1)
                    (SemTy.restrict (A := SemTy.nat) (Nat.le_refl j)
                      (ULift.up ((d + 1) * ans.2.2.2.down)))⟩) =
            StepLift.ret (M.reanchorAns (A := SemTy.nat) hj ans.2.1.proof j (Nat.le_refl j)
              ⟨ans.1, ⟨by simpa using World.le_refl ans.1⟩, ans.2.2.1,
                (ULift.up ((d + 1) * ans.2.2.2.down) : SemTy.eval j SemTy.nat ans.1)⟩) := by
          intro j hj ans
          rw [StepLift.map_ret]
          simp [SemTy.nat, SemTy.map_const, SemTy.restrict_const]
        refine (congrArg (StepLift.bind _) ?_).trans (StepLift.bind_ret_post _ _)
        funext j hj ans
        exact hcont j hj ans
      rw [hpost_bind, StepLift.extractBy_map]
      dsimp only [M.reanchorAns]
      have hpost := StepLift.extractBy_post (fun _ _ ans => ans.2.2.2.down) (fun v => (d + 1) * v)
        (knotFactBody r_q q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
          (ULift.up d) q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
          (TotHeap.update (A := KnotFn) (TotHeap.trunc h₀) l hl_tr
            (CellVal.nextVal (knotFactBody r_q))))
      have hex := knotFactBody_extract d q hdq w'.trunc l hl_tr (TotHeap.trunc h₀)
      have hcomb : StepLift.extractBy (fun _ _ x => (d + 1) * x.2.2.2.down)
          (knotFactBody r_q q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
            (ULift.up d) q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
            (TotHeap.update (A := KnotFn) (TotHeap.trunc h₀) l hl_tr
              (CellVal.nextVal (knotFactBody r_q)))) =
          some (d, (d + 1) * fact d) := by
        refine hpost.trans ?_
        have hex' : StepLift.extractBy (fun _ _ ans => ans.2.2.2.down)
          (knotFactBody r_q q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
            (ULift.up d) q (Nat.le_refl q) w'.trunc (by simpa using World.le_refl w'.trunc)
            (TotHeap.update (A := KnotFn) (TotHeap.trunc h₀) l hl_tr
              (CellVal.nextVal (knotFactBody r_q)))) = some (d, fact d) := hex
        rw [hex']
        rfl
      rw [hcomb]
      simp [fact]

theorem StepLift.extractBy_stepSucc {α : Type 0} {n : Nat}
    {X : (m : Nat) → m ≤ n + 1 → Type 1}
    (proj : ∀ (m : Nat) (hm : m ≤ n + 1), X m hm → α)
    (c' : StepLift n (fun j hj => X j (Nat.le_succ_of_le hj))) :
    StepLift.extractBy proj (StepLift.stepSucc c') =
      (StepLift.extractBy (fun j hj x => proj j (Nat.le_succ_of_le hj) x) c').map
        (fun sv => (sv.1 + 1, sv.2)) := by
  dsimp only [StepLift.stepSucc, StepLift.extractBy]
  cases StepLift.extractBy (fun j hj x => proj j (Nat.le_succ_of_le hj) x) c' <;> rfl

/-- **Parametric Closed Execution Theorem (`landinFact_runClosed`)**:
For EVERY `x, extra : Nat`, running `landinFact x` on `(∅, ∅)` at stage `n = x + 1 + extra`
terminates in **exact step count `x + 1`** (`1` top-level `get r` + `x` recursive `get r`s,
**0** steps for `new` and backpatching `set`!) and returns `fact x`! -/
theorem landinFact_runClosed (x extra : Nat) :
    M.runClosed (landinFact (n := (x + extra) + 1) (w := World.empty ((x + extra) + 1)) x) =
      some (x + 1, fact x) := by
  let q := x + extra
  let w₀ := World.empty (q + 1)
  let l := w₀.fresh
  let w₁ := w₀.insert l KnotFn
  have hl₁ : w₁.cells l = some KnotFn := by simp [w₁]
  let hk_le : q ≤ q + 1 := Nat.le_succ_of_le (Nat.le_refl q)
  have hl_tr : w₁.trunc.cells l = some (SemTy.nextAt q KnotFn) :=
    World.trunc_cells_nextAt q w₁ l KnotFn hl₁
  let r₁ : SemTy.eval (q + 1) (.ref KnotFn) w₁ := ⟨⟨l, hl₁⟩⟩
  let r_q : SemTy.eval q (.ref KnotFn) w₁.trunc := ⟨⟨l, hl_tr⟩⟩
  have hr_q_eq : SemTy.map (World.le_refl w₁.trunc) (SemTy.restrict hk_le r₁) = r_q := by
    simp [r₁, r_q, SemTy.restrict]
  dsimp only [M.runClosed, landinFact]
  simp only [M.bind, M.seq, M.new, M.set, M.get,
    SemTy.eval_comp_map_restrict, knotFactBody_map_restrict,
    StepLift.bind_ret, StepLift.bind_stepSucc, StepLift.map_stepSucc, StepLift.map_map]
  rw [StepLift.extractBy_stepSucc, StepLift.extractBy_map]
  dsimp only [knotInvokeCont, M.reanchorAns]
  let h_alloc := TotHeap.alloc (Heaplet.empty w₀) (A := KnotFn)
    (CellVal.nextVal (SemTy.map (World.le_trans (by simpa using World.le_refl w₀) (World.le_insert_fresh w₀ KnotFn))
      (SemTy.restrict (Nat.le_refl (q + 1)) dummyKnotFn)))
  have hget_top :
      CellVal.toEval ((TotHeap.update (A := KnotFn) h_alloc l hl₁
        (CellVal.nextVal (knotFactBody r₁))).get l KnotFn hl₁) =
      knotFactBody r_q := by
    change CellVal.toEval ((TotHeap.update (A := KnotFn) h_alloc l hl₁
      (CellVal.nextVal (knotFactBody r₁))).get l (SemTy.nextAt (q + 1) KnotFn) hl₁) =
      knotFactBody r_q
    rw [TotHeap.update_same (A := KnotFn) h_alloc l hl₁ (CellVal.nextVal (knotFactBody r₁))]
    dsimp only [CellVal.nextVal]
    rw [CellVal.toEval_ofEval]
    have hmr := knotFactBody_map_restrict hk_le (World.le_refl w₁.trunc) r₁
    rw [SemTy.map_refl, hr_q_eq] at hmr
    exact hmr
  have htrunc_top :
      TotHeap.trunc (TotHeap.update (A := KnotFn) h_alloc l hl₁
        (CellVal.nextVal (knotFactBody r₁))) =
      TotHeap.update (A := KnotFn) (TotHeap.trunc h_alloc) l hl_tr
        (CellVal.nextVal (knotFactBody r_q)) := by
    rw [TotHeap.trunc_update]
    have hmr := knotFactBody_map_restrict hk_le (World.le_refl w₁.trunc) r₁
    rw [SemTy.map_refl, hr_q_eq] at hmr
    rw [hmr]
  simp only [SemTy.restrict_refl_map]
  rw [hget_top, htrunc_top]
  have hextr := knotFactBody_extract x q (Nat.le_add_right x extra) w₁.trunc l hl_tr (TotHeap.trunc h_alloc)
  exact congrArg (Option.map (fun sv => (sv.1 + 1, sv.2))) hextr

/-- Concrete instantiation at `x = 4`, stage `n = 6` (`extra = 1`, so `5 ≤ 5` steps
with 1 step of spare horizon!): returns `(5, 24)` (`4! = 24`)! -/
theorem landinFact_run_4 :
    M.runClosed (landinFact (n := 6) (w := World.empty 6) 4) = some (5, 24) :=
  landinFact_runClosed 4 1

/-! ## Lean 4 Kernel Universe & Impredicativity Barrier Witnesses -/

/-- **Barrier 1 (`Prop` proof irrelevance collapses multi-value program types)**:
Lean 4's sole impredicative universe `Prop` (`Sort 0`) enforces definitional proof irrelevance
(`∀ x y : P, x = y`), so `Bool` cannot retract through any `P : Prop`—preventing TULIP's
computational `Set` from being interpreted in `Prop`. -/
theorem prop_collapses_program_values :
    ¬ ∃ (P : Prop) (encode : Bool → P) (decode : P → Bool), ∀ b, decode (encode b) = b := by
  rintro ⟨P, encode, decode, hretr⟩
  have h1 : decode (encode true) = true := hretr true
  have h2 : decode (encode false) = false := hretr false
  have heq : encode true = encode false := rfl
  rw [heq, h2] at h1
  exact Bool.noConfusion h1

/-- **Barrier 2 (Cantor non-surjection for predicates)**:
No carrier `U : Type u` admits a surjection `U → (U → Prop)` (or `U → (U → Bool)`),
witnessing why unstratified logical predicate spaces `A → prop` cannot embed back into
program types `SemPType` (`ι = p` vs. `ι = ℓ`). -/
theorem cantor_no_predicate_surjection (U : Type u) :
    ¬ ∃ (f : U → (U → Prop)), ∀ (P : U → Prop), ∃ x : U, f x = P := by
  rintro ⟨f, hsurj⟩
  rcases hsurj (fun x => ¬ f x x) with ⟨x₀, hx₀⟩
  have hx : f x₀ x₀ = (¬ f x₀ x₀) := congrFun hx₀ x₀
  have hnot : ¬ f x₀ x₀ := fun h => by
    have h' : ¬ f x₀ x₀ := Eq.mp hx h
    exact h' h
  exact hnot (Eq.mpr hx hnot)

end Tulip
