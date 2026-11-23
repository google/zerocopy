-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import TulipModel.Monad

/-!
# Day-Convolution BI-Hyperdoctrine, Modalities (`□`, `▷`), Points-To, and Löb Induction

Constructs TULIP's semantic assertion logic `BIProp n w` (`ℬ = [pH, Prop_𝕎]` in
`Psh(ωᵒᵖ)`, `paper.tex:1580–1972`) and proves all core intuitionistic affine
separation-logic and guarded-modality laws:
- Heyting connectives (`top`, `bot`, `pure`, `and`, `or`, `imp`, `forallSem`, `existsSem`)
- Day-convolution BI connectives (`emp = top`, `sep`, `wand`)
- Persistence modality `persist` (`□`) and later modality `later` (`▷`)
- Singleton-heap representable `pointsTo` (`[ℓ ↦ a]`)
- `bi_sep_comm`, `bi_sep_assoc`, `bi_wand_adj`, `bi_persist_dup`, `bi_loeb`
-/

namespace Tulip

/-- Helper combining two world-extension steps across stage restriction. -/
theorem World.step_le_trans {k m n : Nat} (hkm : k ≤ m) (hmn : m ≤ n)
    {w : World n} {w₁ : World m} {w₂ : World k}
    (hw₁ : World.Le (w.restrict hmn) w₁)
    (hw₂ : World.Le (w₁.restrict hkm) w₂) :
    World.Le (w.restrict (Nat.le_trans hkm hmn)) w₂ := by
  rw [← World.restrict_trans hkm hmn w]
  exact World.le_trans (World.restrict_mono hkm hw₁) hw₂

/-- A semantic BI-proposition `BIProp n w` anchored at stage `n` and world `w`:
an intuitionistic proposition over `(m ≤ n, w' ≥ w|_m, h : ParHeap m w')` that is
antitone in step-index `m`, monotone in world `w'`, and monotone in the affine
partial-heap extension order `ParHeap.Le`. -/
structure BIProp (n : Nat) (w : World n) : Type 1 where
  holds : ∀ (m : Nat) (hm : m ≤ n) (w' : World m),
            World.Le (w.restrict hm) w' → ParHeap m w' → Prop
  mono  : ∀ {m₁ m₂ : Nat} (hm12 : m₁ ≤ m₂) (hm2 : m₂ ≤ n)
            {w₁ : World m₂} {w₂ : World m₁}
            (hw₁ : World.Le (w.restrict hm2) w₁)
            (hw12 : World.Le (w₁.restrict hm12) w₂)
            {h₁ : ParHeap m₂ w₁} {h₂ : ParHeap m₁ w₂},
            ParHeap.Le ((h₁.restrict hm12).map hw12) h₂ →
            holds m₂ hm2 w₁ hw₁ h₁ →
            holds m₁ (Nat.le_trans hm12 hm2) w₂
              (World.step_le_trans hm12 hm2 hw₁ hw12) h₂

@[ext]
theorem BIProp.ext {n : Nat} {w : World n} {P Q : BIProp n w}
    (h : ∀ m hm w' hw' hp, P.holds m hm w' hw' hp ↔ Q.holds m hm w' hw' hp) :
    P = Q := by
  rcases P with ⟨pH, _⟩
  rcases Q with ⟨qH, _⟩
  have heq : pH = qH := by
    funext m hm w' hw' hp
    exact propext (h m hm w' hw' hp)
  subst heq
  rfl

/-- Entailment `P ⊢ Q` in `BIProp n w` (`paper.tex:1644`). -/
def BIProp.Entails {n : Nat} {w : World n} (P Q : BIProp n w) : Prop :=
  ∀ m (hm : m ≤ n) (w' : World m) (hw' : World.Le (w.restrict hm) w') (h : ParHeap m w'),
    P.holds m hm w' hw' h → Q.holds m hm w' hw' h

theorem BIProp.entails_refl {n : Nat} {w : World n} (P : BIProp n w) :
    BIProp.Entails P P :=
  fun _ _ _ _ _ hp => hp

theorem BIProp.entails_trans {n : Nat} {w : World n} {P Q R : BIProp n w}
    (hPQ : BIProp.Entails P Q) (hQR : BIProp.Entails Q R) :
    BIProp.Entails P R :=
  fun m hm w' hw' h hp => hQR m hm w' hw' h (hPQ m hm w' hw' h hp)

theorem BIProp.equiv_iff_eq {n : Nat} {w : World n} {P Q : BIProp n w} :
    (BIProp.Entails P Q ∧ BIProp.Entails Q P) ↔ P = Q := by
  constructor
  · rintro ⟨h1, h2⟩
    ext m hm w' hw' hp
    exact ⟨h1 m hm w' hw' hp, h2 m hm w' hw' hp⟩
  · rintro rfl
    exact ⟨BIProp.entails_refl P, BIProp.entails_refl P⟩

/-- Specialized heap-extension monotonicity at fixed `(m, w')`. -/
theorem BIProp.mono_heap {n : Nat} {w : World n} (P : BIProp n w)
    {m : Nat} (hm : m ≤ n) {w' : World m} (hw' : World.Le (w.restrict hm) w')
    {h₁ h₂ : ParHeap m w'} (hh : ParHeap.Le h₁ h₂) :
    P.holds m hm w' hw' h₁ → P.holds m hm w' hw' h₂ := by
  have h1 : ParHeap.Le ((h₁.restrict (Nat.le_refl m)).map (World.restrict_refl_le w')) h₂ := by
    rw [ParHeap.restrict_refl_map]
    exact hh
  exact P.mono (Nat.le_refl m) hm hw' (World.restrict_refl_le w') h1

/-- Specialized world-extension monotonicity at fixed stage `m`. -/
theorem BIProp.mono_world {n : Nat} {w : World n} (P : BIProp n w)
    {m : Nat} (hm : m ≤ n) {w₁ w₂ : World m}
    (hw₁ : World.Le (w.restrict hm) w₁) (hw12 : World.Le w₁ w₂)
    (h : ParHeap m w₁) :
    P.holds m hm w₁ hw₁ h →
      P.holds m hm w₂ (World.le_trans hw₁ hw12) (h.map hw12) := by
  have hw12' : World.Le (w₁.restrict (Nat.le_refl m)) w₂ :=
    World.le_trans (World.restrict_refl_le w₁) hw12
  have hh : ParHeap.Le ((h.restrict (Nat.le_refl m)).map hw12') (h.map hw12) := by
    have heq : (h.restrict (Nat.le_refl m)).map hw12' = h.map hw12 := by
      have h0 := ParHeap.restrict_refl_map h
      have := congrArg (ParHeap.map hw12) h0
      rw [ParHeap.map_trans] at this
      exact this
    rw [heq]
    exact ParHeap.le_refl _
  exact P.mono (Nat.le_refl m) hm hw₁ hw12' hh

/-- Specialized stage-restriction monotonicity from `m₂` down to `m₁ ≤ m₂`. -/
theorem BIProp.mono_stage {n : Nat} {w : World n} (P : BIProp n w)
    {m₁ m₂ : Nat} (hm12 : m₁ ≤ m₂) (hm2 : m₂ ≤ n)
    {w₁ : World m₂} (hw₁ : World.Le (w.restrict hm2) w₁) (h : ParHeap m₂ w₁) :
    P.holds m₂ hm2 w₁ hw₁ h →
      P.holds m₁ (Nat.le_trans hm12 hm2) (w₁.restrict hm12)
        (World.step_le_trans hm12 hm2 hw₁ (World.le_refl _)) (h.restrict hm12) := by
  apply P.mono hm12 hm2 hw₁ (World.le_refl _)
  rw [ParHeap.map_refl]
  exact ParHeap.le_refl _

/-- Covariant reindexing of `BIProp n w₁` along `w₁ ≤ w₂`. -/
noncomputable def BIProp.map {n : Nat} {w₁ w₂ : World n} (hle : World.Le w₁ w₂)
    (P : BIProp n w₁) : BIProp n w₂ where
  holds m hm w' hw' h :=
    P.holds m hm w' (World.le_trans (World.restrict_mono hm hle) hw') h
  mono := by
    intro m₁ m₂ hm12 hm2 u₁ u₂ hu₁ hu12 h₁ h₂ hh hp
    exact P.mono hm12 hm2 (World.le_trans (World.restrict_mono hm2 hle) hu₁) hu12 hh hp

/-- Stage restriction of `BIProp n w` along `m ≤ n`. -/
noncomputable def BIProp.restrict {m n : Nat} (hmn : m ≤ n) {w : World n}
    (P : BIProp n w) : BIProp m (w.restrict hmn) where
  holds j hj w' hw' h :=
    P.holds j (Nat.le_trans hj hmn) w'
      (by rw [← World.restrict_trans hj hmn w]; exact hw') h
  mono := by
    intro j₁ j₂ hj12 hj2 u₁ u₂ hu₁ hu12 h₁ h₂ hh hp
    exact P.mono hj12 (Nat.le_trans hj2 hmn)
      (by rw [← World.restrict_trans hj2 hmn w]; exact hu₁) hu12 hh hp

/-! ## Parameterized Predicates `BIPred n w A` (`ℬ^A(w)`) -/

/-- A semantic predicate `Φ : BIPred n w A` over program values of type `A`. -/
structure BIPred (n : Nat) (w : World n) (A : SemTy) : Type 1 where
  holds : ∀ (m : Nat) (hm : m ≤ n) (w' : World m),
            World.Le (w.restrict hm) w' → SemTy.eval m A w' → ParHeap m w' → Prop
  mono  : ∀ {m₁ m₂ : Nat} (hm12 : m₁ ≤ m₂) (hm2 : m₂ ≤ n)
            {w₁ : World m₂} {w₂ : World m₁}
            (hw₁ : World.Le (w.restrict hm2) w₁)
            (hw12 : World.Le (w₁.restrict hm12) w₂)
            (a : SemTy.eval m₂ A w₁)
            {h₁ : ParHeap m₂ w₁} {h₂ : ParHeap m₁ w₂},
            ParHeap.Le ((h₁.restrict hm12).map hw12) h₂ →
            holds m₂ hm2 w₁ hw₁ a h₁ →
            holds m₁ (Nat.le_trans hm12 hm2) w₂
              (World.step_le_trans hm12 hm2 hw₁ hw12)
              (SemTy.map hw12 (SemTy.restrict hm12 a)) h₂

/-- Apply a predicate `Φ : BIPred n w A` to a value `a : A_n(w)` to get a `BIProp n w`. -/
noncomputable def BIPred.app {n : Nat} {w : World n} {A : SemTy}
    (Φ : BIPred n w A) (a : SemTy.eval n A w) : BIProp n w where
  holds m hm w' hw' h :=
    Φ.holds m hm w' hw' (SemTy.map hw' (SemTy.restrict hm a)) h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hp
    have hstep := Φ.mono hm12 hm2 hw₁ hw12
      (SemTy.map hw₁ (SemTy.restrict hm2 a)) hh hp
    have heq : SemTy.map hw12 (SemTy.restrict hm12 (SemTy.map hw₁ (SemTy.restrict hm2 a))) =
        SemTy.map (World.step_le_trans hm12 hm2 hw₁ hw12)
          (SemTy.restrict (Nat.le_trans hm12 hm2) a) := by
      rw [SemTy.restrict_map_comm, SemTy.map_trans]
      have htr := SemTy.restrict_trans_map hm12 hm2 (World.restrict_trans_le hm12 hm2 w) a
      rw [← htr, SemTy.map_trans]
    rw [heq] at hstep
    exact hstep

/-- Evaluate a predicate `Φ : BIPred n w A` at a sub-stage `m ≤ n`, `w' ≥ w|_m`, `a : A_m(w')`. -/
noncomputable def BIPred.atVal {n : Nat} {w : World n} {A : SemTy} (Φ : BIPred n w A)
    {m : Nat} (hm : m ≤ n) {w' : World m} (hw' : World.Le (w.restrict hm) w')
    (a : SemTy.eval m A w') : BIProp m w' where
  holds j hj w₂ hw₂ h :=
    Φ.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂)
      (SemTy.map hw₂ (SemTy.restrict hj a)) h
  mono := by
    intro j₁ j₂ hj12 hj2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hp
    have hstep := Φ.mono hj12 (Nat.le_trans hj2 hm)
      (World.step_le_trans hj2 hm hw' hw₁) hw12
      (SemTy.map hw₁ (SemTy.restrict hj2 a)) hh hp
    have heq : SemTy.map hw12 (SemTy.restrict hj12 (SemTy.map hw₁ (SemTy.restrict hj2 a))) =
        SemTy.map (World.step_le_trans hj12 hj2 hw₁ hw12)
          (SemTy.restrict (Nat.le_trans hj12 hj2) a) := by
      rw [SemTy.restrict_map_comm, SemTy.map_trans]
      have htr := SemTy.restrict_trans_map hj12 hj2 (World.restrict_trans_le hj12 hj2 w') a
      rw [← htr, SemTy.map_trans]
    rw [heq] at hstep
    exact hstep

theorem BIPred.mono_heap {n : Nat} {w : World n} {A : SemTy} (Φ : BIPred n w A)
    {m : Nat} (hm : m ≤ n) {w' : World m} (hw' : World.Le (w.restrict hm) w')
    (a : SemTy.eval m A w') {h₁ h₂ : ParHeap m w'} (hh : ParHeap.Le h₁ h₂) :
    Φ.holds m hm w' hw' a h₁ → Φ.holds m hm w' hw' a h₂ := by
  have hp := (Φ.atVal hm hw' a).mono_heap (Nat.le_refl m) (World.restrict_refl_le w') hh
  simpa [BIPred.atVal, SemTy.restrict_refl_map] using hp

/-- Constant `BIPred` ignoring its argument. -/
noncomputable def BIPred.const {n : Nat} {w : World n} (A : SemTy) (P : BIProp n w) : BIPred n w A where
  holds m hm w' hw' _ h := P.holds m hm w' hw' h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 _ h₁ h₂ hh hp
    exact P.mono hm12 hm2 hw₁ hw12 hh hp

/-- Pure postcondition predicate on `SemTy.const α`: `fun v => P v.down`. -/
noncomputable def BIPred.pureConst {n : Nat} {w : World n} {α : Type 0} (P : α → Prop) :
    BIPred n w (.const α) where
  holds _ _ _ _ v _ := P v.down
  mono := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ hp
    simpa [SemTy.restrict, SemTy.map] using hp

/-- Fused restriction-and-map lemma for partial heaps across two stage/world steps. -/
theorem ParHeap.restrict_map_step {j m₁ m₂ : Nat} (hj : j ≤ m₁) (hm12 : m₁ ≤ m₂)
    {w₁ : World m₂} {w₂ : World m₁} {w₃ : World j}
    (hw12 : World.Le (w₁.restrict hm12) w₂) (hw₃ : World.Le (w₂.restrict hj) w₃)
    (h₁ : ParHeap m₂ w₁) :
    (((h₁.restrict hm12).map hw12).restrict hj).map hw₃ =
      (h₁.restrict (Nat.le_trans hj hm12)).map (World.step_le_trans hj hm12 hw12 hw₃) := by
  rw [ParHeap.restrict_map_comm, ParHeap.map_trans,
    ← ParHeap.restrict_trans_map hj hm12 h₁, ParHeap.map_trans]

/-! ## Heyting & Day-Convolution BI Connectives (`paper.tex:1890–1972`) -/

namespace BIProp

/-- Truth / affine empty-heap unit `⊤ = emp` (`paper.tex:580`). -/
noncomputable def top (n : Nat) (w : World n) : BIProp n w where
  holds _ _ _ _ _ := True
  mono := by intros; trivial

/-- Alias `emp = top` in affine separation logic. -/
noncomputable abbrev emp (n : Nat) (w : World n) : BIProp n w := top n w

/-- Falsity `⊥`. -/
noncomputable def bot (n : Nat) (w : World n) : BIProp n w where
  holds _ _ _ _ _ := False
  mono := by intros; contradiction

/-- Pure Lean `Prop` lifted into `BIProp n w`. -/
noncomputable def pure (n : Nat) (w : World n) (P : Prop) : BIProp n w where
  holds _ _ _ _ _ := P
  mono := by intro _ _ _ _ _ _ _ _ _ _ _ hp; exact hp

/-- Conjunction `P ∧ Q`. -/
noncomputable def and {n : Nat} {w : World n} (P Q : BIProp n w) : BIProp n w where
  holds m hm w' hw' h := P.holds m hm w' hw' h ∧ Q.holds m hm w' hw' h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hpq
    exact ⟨P.mono hm12 hm2 hw₁ hw12 hh hpq.1, Q.mono hm12 hm2 hw₁ hw12 hh hpq.2⟩

/-- Disjunction `P ∨ Q`. -/
noncomputable def or {n : Nat} {w : World n} (P Q : BIProp n w) : BIProp n w where
  holds m hm w' hw' h := P.holds m hm w' hw' h ∨ Q.holds m hm w' hw' h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hpq
    exact hpq.elim (fun hp => Or.inl (P.mono hm12 hm2 hw₁ hw12 hh hp))
                   (fun hq => Or.inr (Q.mono hm12 hm2 hw₁ hw12 hh hq))

/-- Intuitionistic Heyting implication `P ⇒ Q` (`paper.tex:1908, 1957`). -/
noncomputable def imp {n : Nat} {w : World n} (P Q : BIProp n w) : BIProp n w where
  holds m hm w' hw' h :=
    ∀ (j : Nat) (hj : j ≤ m) (w₂ : World j) (hw₂ : World.Le (w'.restrict hj) w₂)
      (h₂ : ParHeap j w₂),
      ParHeap.Le ((h.restrict hj).map hw₂) h₂ →
      P.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) h₂ →
      Q.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) h₂
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh himp j hj w₃ hw₃ h₃ hh₃ hp
    have h_chain : ParHeap.Le ((h₁.restrict (Nat.le_trans hj hm12)).map
        (World.step_le_trans hj hm12 hw12 hw₃)) h₃ := by
      rw [← ParHeap.restrict_map_step hj hm12 hw12 hw₃ h₁]
      exact ParHeap.le_trans (ParHeap.map_mono hw₃ (ParHeap.restrict_mono hj hh)) hh₃
    exact himp j (Nat.le_trans hj hm12) w₃ (World.step_le_trans hj hm12 hw12 hw₃) h₃ h_chain hp

/-- Universal quantification `∀ x : A, Φ x` (`paper.tex:1912, 1961`). -/
noncomputable def forallSem {n : Nat} {w : World n} {A : SemTy} (Φ : BIPred n w A) : BIProp n w where
  holds m hm w' hw' h :=
    ∀ (j : Nat) (hj : j ≤ m) (w₂ : World j) (hw₂ : World.Le (w'.restrict hj) w₂)
      (h₂ : ParHeap j w₂) (a : SemTy.eval j A w₂),
      ParHeap.Le ((h.restrict hj).map hw₂) h₂ →
      Φ.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) a h₂
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hall j hj w₃ hw₃ h₃ a hh₃
    have h_chain : ParHeap.Le ((h₁.restrict (Nat.le_trans hj hm12)).map
        (World.step_le_trans hj hm12 hw12 hw₃)) h₃ := by
      rw [← ParHeap.restrict_map_step hj hm12 hw12 hw₃ h₁]
      exact ParHeap.le_trans (ParHeap.map_mono hw₃ (ParHeap.restrict_mono hj hh)) hh₃
    exact hall j (Nat.le_trans hj hm12) w₃ (World.step_le_trans hj hm12 hw12 hw₃) h₃ a h_chain

/-- Existential quantification `∃ x : A, Φ x` (`paper.tex:1915, 1965`). -/
noncomputable def existsSem {n : Nat} {w : World n} {A : SemTy} (Φ : BIPred n w A) : BIProp n w where
  holds m hm w' hw' h := ∃ a : SemTy.eval m A w', Φ.holds m hm w' hw' a h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh ⟨a, ha⟩
    exact ⟨SemTy.map hw12 (SemTy.restrict hm12 a), Φ.mono hm12 hm2 hw₁ hw12 a hh ha⟩

/-- Separating conjunction `P ∗ Q` via Day convolution (`paper.tex:1792, 1926`):
`h ⊩ P ∗ Q ⇔ ∃ h₁ h₂, h₁ # h₂ ∧ h = h₁ · h₂ ∧ h₁ ⊩ P ∧ h₂ ⊩ Q`. -/
noncomputable def sep {n : Nat} {w : World n} (P Q : BIProp n w) : BIProp n w where
  holds m hm w' hw' h :=
    ∃ h₁ h₂ : ParHeap m w',
      ParHeap.Disjoint h₁ h₂ ∧ h = h₁.union h₂ ∧
      P.holds m hm w' hw' h₁ ∧ Q.holds m hm w' hw' h₂
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh ⟨p₁, p₂, hd12, heq_h₁, hp₁, hp₂⟩
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
    refine ⟨q₁, q₂, hd_q, h_union_eq, ?_, ?_⟩
    · exact P.mono hm12 hm2 hw₁ hw12 (ParHeap.le_refl q₁) hp₁
    · refine Q.mono hm12 hm2 hw₁ hw12 ⟨h_ext, ?_, rfl⟩ hp₂
      intro l
      rcases hd_ext l with de1 | de2
      · simp only [ParHeap.map_dom, ParHeap.restrict_dom, ParHeap.union_dom,
          Bool.or_eq_false_iff] at de1
        left; simp [de1.2]
      · right; exact de2

/-- Separating implication / magic wand `P -∗ Q` (`paper.tex:1930, 1960`). -/
noncomputable def wand {n : Nat} {w : World n} (P Q : BIProp n w) : BIProp n w where
  holds m hm w' hw' h :=
    ∀ (j : Nat) (hj : j ≤ m) (w₂ : World j) (hw₂ : World.Le (w'.restrict hj) w₂)
      (h' : ParHeap j w₂),
      ParHeap.Disjoint ((h.restrict hj).map hw₂) h' →
      P.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) h' →
      Q.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂)
        (((h.restrict hj).map hw₂).union h')
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hwand j hj w₃ hw₃ h' hd' hp'
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
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12
        left; exact d12.1
      · right; exact d3
    have hq_base := hwand j (Nat.le_trans hj hm12) w₃
      (World.step_le_trans hj hm12 hw12 hw₃) h' hd_h1_hp hp'
    have hle_res : ParHeap.Le (h₁_w₃.union h') ((h₁_w₃.union h_ext_w₃).union h') := by
      have hd_ext_hp : ParHeap.Disjoint (h₁_w₃.union h') h_ext_w₃ := by
        intro l
        rcases hd' l with d12 | d3
        · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12
          right; exact d12.2
        · have hd_e := hd_ext l
          simp only [ParHeap.map_dom, ParHeap.restrict_dom] at hd_e
          rcases hd_e with e1 | e2
          · left; simp [h₁_w₃, e1, d3]
          · right; simp [h_ext_w₃, e2]
      refine ⟨h_ext_w₃, hd_ext_hp, ?_⟩
      rw [ParHeap.union_assoc, ParHeap.union_assoc,
        ParHeap.union_comm (show ParHeap.Disjoint h_ext_w₃ h' by
          intro l
          rcases hd' l with d12 | d3
          · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12
            left; exact d12.2
          · right; exact d3)]
    exact Q.mono_heap (Nat.le_trans hj (Nat.le_trans hm12 hm2))
      (World.step_le_trans hj (Nat.le_trans hm12 hm2)
        (World.step_le_trans hm12 hm2 hw₁ hw12) hw₃)
      hle_res hq_base

/-- Persistence modality `□ P` (`paper.tex:1808, 1923`): reindexes along `h ↦ ∅`. -/
noncomputable def persist {n : Nat} {w : World n} (P : BIProp n w) : BIProp n w where
  holds m hm w' hw' _ := P.holds m hm w' hw' (ParHeap.empty m w')
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 _ _ _ hp
    have hemp : ((ParHeap.empty m₂ w₁).restrict hm12).map hw12 = ParHeap.empty m₁ w₂ := by
      refine ParHeap.ext (fun _ => by simp) ?_
      intro _ _ hd _
      simp at hd
    exact P.mono hm12 hm2 hw₁ hw12 (by rw [hemp]; exact ParHeap.le_refl _) hp

/-- Guarded later modality `▷ P` (`paper.tex:1615–1618`): holds trivially at stage `0`,
and at stage `k + 1` holds iff `P` holds at stage `k` on `(w'.trunc, h.trunc)`. -/
noncomputable def later {n : Nat} {w : World n} (P : BIProp n w) : BIProp n w where
  holds m hm w' hw' h :=
    match m, hm, w', hw', h with
    | 0,     _,  _,  _,   _ => True
    | k + 1, hm, w', hw', h =>
        P.holds k (Nat.le_of_succ_le hm) w'.trunc
          (World.step_le_trans (Nat.le_succ_of_le (Nat.le_refl k)) hm hw' (World.le_refl _))
          (h.restrict (Nat.le_succ_of_le (Nat.le_refl k)))
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hp
    cases m₁ with
    | zero => trivial
    | succ k₁ =>
      cases m₂ with
      | zero => omega
      | succ k₂ =>
        dsimp only at hp ⊢
        have hk12 : k₁ ≤ k₂ := Nat.le_of_succ_le_succ hm12
        have hw_tr : World.Le (w₁.trunc.restrict hk12) w₂.trunc := by
          have heq : w₁.trunc.restrict hk12 = (w₁.restrict hm12).trunc := by
            simp [World.trunc]
          rw [heq]
          exact World.restrict_mono _ hw12
        have hh_tr : ParHeap.Le
            (((h₁.restrict (Nat.le_succ_of_le (Nat.le_refl k₂))).restrict hk12).map hw_tr)
            (h₂.restrict (Nat.le_succ_of_le (Nat.le_refl k₁))) := by
          have hmon := ParHeap.restrict_mono (Nat.le_succ_of_le (Nat.le_refl k₁)) hh
          rw [ParHeap.restrict_map_comm] at hmon
          have h1 := ParHeap.restrict_trans_map hk12 (Nat.le_succ_of_le (Nat.le_refl k₂)) h₁
          have h2 := ParHeap.restrict_trans_map (Nat.le_succ_of_le (Nat.le_refl k₁)) hm12 h₁
          have h_mid : h₁.restrict (Nat.le_trans hk12 (Nat.le_succ_of_le (Nat.le_refl k₂))) =
              h₁.restrict (Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl k₁)) hm12) := rfl
          have h_eq_mid :
              ((h₁.restrict (Nat.le_succ_of_le (Nat.le_refl k₂))).restrict hk12).map
                (World.restrict_trans_le hk12 (Nat.le_succ_of_le (Nat.le_refl k₂)) w₁) =
              ((h₁.restrict hm12).restrict (Nat.le_succ_of_le (Nat.le_refl k₁))).map
                (World.restrict_trans_le (Nat.le_succ_of_le (Nat.le_refl k₁)) hm12 w₁) :=
            h1.trans (h_mid.trans h2.symm)
          have h_push := congrArg
            (ParHeap.map (World.le_trans
              (by rw [← World.restrict_trans]; exact World.le_refl _)
              (World.restrict_mono (Nat.le_succ_of_le (Nat.le_refl k₁)) hw12))) h_eq_mid
          rw [ParHeap.map_trans, ParHeap.map_trans] at h_push
          have h_lhs : World.le_trans
              (World.restrict_trans_le hk12 (Nat.le_succ_of_le (Nat.le_refl k₂)) w₁)
              (World.le_trans (by rw [← World.restrict_trans]; exact World.le_refl _)
                (World.restrict_mono (Nat.le_succ_of_le (Nat.le_refl k₁)) hw12)) = hw_tr := rfl
          have h_rhs : World.le_trans
              (World.restrict_trans_le (Nat.le_succ_of_le (Nat.le_refl k₁)) hm12 w₁)
              (World.le_trans (by rw [← World.restrict_trans]; exact World.le_refl _)
                (World.restrict_mono (Nat.le_succ_of_le (Nat.le_refl k₁)) hw12)) =
              World.restrict_mono (Nat.le_succ_of_le (Nat.le_refl k₁)) hw12 := rfl
          rw [h_lhs, h_rhs] at h_push
          rw [h_push]
          exact hmon
        exact P.mono hk12 (Nat.le_of_succ_le hm2)
          (World.step_le_trans (Nat.le_succ_of_le (Nat.le_refl k₂)) hm2 hw₁ (World.le_refl _))
          hw_tr hh_tr hp

/-- Singleton-heap representable `pointsTo r a` (`[r ↦ a]`, `paper.tex:1816–1820`):
`h ⊩ [r ↦ a] ⇔ {r ↦ next a} ≤ h`. -/
noncomputable def pointsTo {n : Nat} {w : World n} {A : SemTy}
    (r : SemTy.eval n (.ref A) w) (a : SemTy.eval n A w) : BIProp n w where
  holds m hm w' hw' h :=
    have hl' : w'.cells r.down.1 = some (SemTy.nextAt m A) :=
      hw' r.down.1 (SemTy.nextAt m A) (by simp [World.restrict_cells, r.down.2])
    ParHeap.Le (ParHeap.singleton r.down.1 hl' (SemTy.map hw' (SemTy.restrict hm a))) h
  mono := by
    intro m₁ m₂ hm12 hm2 w₁ w₂ hw₁ hw12 h₁ h₂ hh hp
    dsimp only at hp ⊢
    have hmon := ParHeap.map_mono hw12 (ParHeap.restrict_mono hm12 hp)
    rw [ParHeap.restrict_singleton, ParHeap.map_singleton] at hmon
    have heq_a : SemTy.map hw12 (SemTy.restrict hm12 (SemTy.map hw₁ (SemTy.restrict hm2 a))) =
        SemTy.map (World.step_le_trans hm12 hm2 hw₁ hw12)
          (SemTy.restrict (Nat.le_trans hm12 hm2) a) := by
      rw [SemTy.restrict_map_comm, SemTy.map_trans]
      have htr := SemTy.restrict_trans_map hm12 hm2 (World.restrict_trans_le hm12 hm2 w) a
      rw [← htr, SemTy.map_trans]
    rw [heq_a] at hmon
    exact ParHeap.le_trans hmon hh

end BIProp

/-! ## Core BI-Hyperdoctrine, Persistence, and Löb Induction Laws -/

/-- Symmetry of separating conjunction (`P ∗ Q = Q ∗ P`, `paper.tex:613`). -/
theorem bi_sep_comm {n : Nat} {w : World n} (P Q : BIProp n w) :
    P.sep Q = Q.sep P := by
  ext m hm w' hw' h
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
    exact ⟨h₂, h₁, hd.symm, ParHeap.union_comm hd, hq, hp⟩
  · rintro ⟨h₂, h₁, hd, rfl, hq, hp⟩
    exact ⟨h₁, h₂, hd.symm, ParHeap.union_comm hd, hp, hq⟩

/-- Associativity of separating conjunction (`(P ∗ Q) ∗ R = P ∗ (Q ∗ R)`, `paper.tex:611`). -/
theorem bi_sep_assoc {n : Nat} {w : World n} (P Q R : BIProp n w) :
    (P.sep Q).sep R = P.sep (Q.sep R) := by
  ext m hm w' hw' h
  constructor
  · rintro ⟨h12, h₃, hd12_3, rfl, ⟨h₁, h₂, hd12, rfl, hp, hq⟩, hr⟩
    have hd23 : ParHeap.Disjoint h₂ h₃ := by
      intro l
      rcases hd12_3 l with d12 | d3
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12
        left; exact d12.2
      · right; exact d3
    have hd1_23 : ParHeap.Disjoint h₁ (h₂.union h₃) := by
      intro l
      rcases hd12 l with d1 | d2
      · left; exact d1
      · rcases hd12_3 l with d12 | d3
        · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d12
          left; exact d12.1
        · right; simp [d2, d3]
    exact ⟨h₁, h₂.union h₃, hd1_23, ParHeap.union_assoc h₁ h₂ h₃, hp,
      ⟨h₂, h₃, hd23, rfl, hq, hr⟩⟩
  · rintro ⟨h₁, h23, hd1_23, rfl, hp, ⟨h₂, h₃, hd23, rfl, hq, hr⟩⟩
    have hd12 : ParHeap.Disjoint h₁ h₂ := by
      intro l
      rcases hd1_23 l with d1 | d23
      · left; exact d1
      · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d23
        right; exact d23.1
    have hd12_3 : ParHeap.Disjoint (h₁.union h₂) h₃ := by
      intro l
      rcases hd23 l with d2 | d3
      · rcases hd1_23 l with d1 | d23
        · left; simp [d1, d2]
        · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at d23
          right; exact d23.2
      · right; exact d3
    exact ⟨h₁.union h₂, h₃, hd12_3, (ParHeap.union_assoc h₁ h₂ h₃).symm,
      ⟨h₁, h₂, hd12, rfl, hp, hq⟩, hr⟩

/-- Unit law of affine separating conjunction (`P ∗ ⊤ = P`, `paper.tex:580`). -/
theorem bi_sep_top {n : Nat} {w : World n} (P : BIProp n w) :
    P.sep (BIProp.top n w) = P := by
  ext m hm w' hw' h
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, _⟩
    exact P.mono_heap hm hw' ⟨h₂, hd, rfl⟩ hp
  · intro hp
    exact ⟨h, ParHeap.empty m w', ParHeap.disjoint_empty_right h,
      (ParHeap.union_empty h).symm, hp, trivial⟩

/-- Monotonicity of separating conjunction (`paper.tex:600–606`). -/
theorem bi_sep_mono {n : Nat} {w : World n} {P P' Q Q' : BIProp n w}
    (hP : BIProp.Entails P P') (hQ : BIProp.Entails Q Q') :
    BIProp.Entails (P.sep Q) (P'.sep Q') := by
  rintro m hm w' hw' h ⟨h₁, h₂, hd, rfl, hp, hq⟩
  exact ⟨h₁, h₂, hd, rfl, hP m hm w' hw' h₁ hp, hQ m hm w' hw' h₂ hq⟩

/-- Day-convolution adjunction `(R ∗ P ⊢ Q) ↔ (R ⊢ P -∗ Q)` (`paper.tex:594–597`). -/
theorem bi_wand_adj {n : Nat} {w : World n} (R P Q : BIProp n w) :
    BIProp.Entails (R.sep P) Q ↔ BIProp.Entails R (P.wand Q) := by
  constructor
  · intro hRPQ m hm w' hw' h hr j hj w₂ hw₂ h' hd hp'
    have hr_w₂ : R.holds j (Nat.le_trans hj hm) w₂
        (World.step_le_trans hj hm hw' hw₂) ((h.restrict hj).map hw₂) :=
      R.mono hj hm hw' hw₂ (ParHeap.le_refl _) hr
    exact hRPQ j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂)
      (((h.restrict hj).map hw₂).union h')
      ⟨(h.restrict hj).map hw₂, h', hd, rfl, hr_w₂, hp'⟩
  · rintro hR_PQ m hm w' hw' h ⟨h₁, h₂, hd, rfl, hr₁, hp₂⟩
    have hwand := hR_PQ m hm w' hw' h₁ hr₁
    have h1_refl : (h₁.restrict (Nat.le_refl m)).map (World.restrict_refl_le w') = h₁ :=
      ParHeap.restrict_refl_map h₁
    have hq := hwand m (Nat.le_refl m) w' (World.restrict_refl_le w') h₂
      (by rw [h1_refl]; exact hd) hp₂
    rw [h1_refl] at hq
    exact hq

/-- Persistence duplication law `□ P ⊢ P ∗ □ P` (`paper.tex:643`), and in fact `□ P = □ P ∗ □ P`. -/
theorem bi_persist_dup {n : Nat} {w : World n} (P : BIProp n w) :
    BIProp.Entails P.persist (P.sep P.persist) := by
  intro m hm w' hw' h hp_emp
  have hp_h : P.holds m hm w' hw' h :=
    P.mono_heap hm hw' (ParHeap.empty_le h) hp_emp
  exact ⟨h, ParHeap.empty m w', ParHeap.disjoint_empty_right h,
    (ParHeap.union_empty h).symm, hp_h, hp_emp⟩

/-- Persistent conjunction-to-separation rule `P ∧ □ Q ⊢ P ∗ □ Q` (`paper.tex:647`). -/
theorem bi_and_persist_sep {n : Nat} {w : World n} (P Q : BIProp n w) :
    BIProp.Entails (P.and Q.persist) (P.sep Q.persist) := by
  rintro m hm w' hw' h ⟨hp, hq_emp⟩
  exact ⟨h, ParHeap.empty m w', ParHeap.disjoint_empty_right h,
    (ParHeap.union_empty h).symm, hp, hq_emp⟩

/-- Introduction rule for `▷`: `P ⊢ ▷ P` (`paper.tex:675`). -/
theorem bi_later_intro {n : Nat} {w : World n} (P : BIProp n w) :
    BIProp.Entails P P.later := by
  intro m hm w' hw' h hp
  cases m with
  | zero => trivial
  | succ k => exact P.mono_stage (Nat.le_succ_of_le (Nat.le_refl k)) hm hw' h hp

/-- Distributivity of `▷` over `∗`: `▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q)` (`paper.tex:681`). -/
theorem bi_later_sep {n : Nat} {w : World n} (P Q : BIProp n w) :
    BIProp.Entails (P.later.sep Q.later) (P.sep Q).later := by
  rintro m hm w' hw' h ⟨h₁, h₂, hd, rfl, hp, hq⟩
  cases m with
  | zero => trivial
  | succ k =>
    refine ⟨h₁.restrict _, h₂.restrict _, ?_, ParHeap.restrict_union _ h₁ h₂, hp, hq⟩
    intro l
    simpa using hd l

/-- Löb induction principle `(▷ P ⇒ P) ⊢ P` (`paper.tex:710`)!
Also implies the external rule `(BIProp.Entails P.later P) → BIProp.Entails ⊤ P`. -/
theorem bi_loeb {n : Nat} {w : World n} (P : BIProp n w) :
    BIProp.Entails (P.later.imp P) P := by
  intro m
  induction m with
  | zero =>
    intro hm w' hw' h himp
    have h_refl : (h.restrict (Nat.le_refl 0)).map (World.restrict_refl_le w') = h :=
      ParHeap.restrict_refl_map h
    exact himp 0 (Nat.le_refl 0) w' (World.restrict_refl_le w') h
      (by rw [h_refl]; exact ParHeap.le_refl h) trivial
  | succ k ih =>
    intro hm w' hw' h himp
    have hk_le : k ≤ k + 1 := Nat.le_succ_of_le (Nat.le_refl k)
    have himp_k : (P.later.imp P).holds k (Nat.le_of_succ_le hm) w'.trunc
        (World.step_le_trans hk_le hm hw' (World.le_refl _)) (h.restrict hk_le) :=
      (P.later.imp P).mono_stage hk_le hm hw' h himp
    have hp_later : P.later.holds (k + 1) hm w' hw' h :=
      ih (Nat.le_of_succ_le hm) w'.trunc
        (World.step_le_trans hk_le hm hw' (World.le_refl _))
        (h.restrict hk_le) himp_k
    have h_refl : (h.restrict (Nat.le_refl (k + 1))).map
        (World.restrict_refl_le w') = h :=
      ParHeap.restrict_refl_map h
    exact himp (k + 1) (Nat.le_refl (k + 1)) w' (World.restrict_refl_le w') h
      (by rw [h_refl]; exact ParHeap.le_refl h) hp_later

/-- External rule form of Löb induction: `(R ∧ ▷ P ⊢ P) → (R ⊢ P)`. -/
theorem bi_loeb_entails {n : Nat} {w : World n} {R P : BIProp n w}
    (hstep : BIProp.Entails (R.and P.later) P) :
    BIProp.Entails R P := by
  refine BIProp.entails_trans ?_ (bi_loeb P)
  intro m hm w' hw' h hr j hj w₂ hw₂ h₂ hh₂ hlat
  have hr₂ : R.holds j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) h₂ :=
    R.mono hj hm hw' hw₂ hh₂ hr
  exact hstep j (Nat.le_trans hj hm) w₂ (World.step_le_trans hj hm hw' hw₂) h₂ ⟨hr₂, hlat⟩

/-- Consistency of the semantic BI-hyperdoctrine (`¬ (⊤ ⊢ ⊥)`, `paper.tex:2149`). -/
theorem bi_consistent (n : Nat) (w : World n) :
    ¬ BIProp.Entails (BIProp.top n w) (BIProp.bot n w) := by
  intro h
  exact h n (Nat.le_refl n) w (World.restrict_refl_le w) (ParHeap.empty n w) trivial

end Tulip
