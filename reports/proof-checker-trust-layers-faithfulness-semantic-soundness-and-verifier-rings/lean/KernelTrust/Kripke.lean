/-
  Toy.KernelTrust.Kripke

  Kripke-style (and one neighbourhood-style) models of `ProvFamily`, used for
  * K4b: consistent rings of consistency proofs once one cross-theory condition
    is dropped;
  * the tightness witnesses for the hypotheses of K4a and K4a-local;
  * positive controls (an open chain of consistency proofs; a ring with one
    unverified link);
  * tightness witnesses for K5 / K5-iff;
  * positive and negative examples for the provability-interface definitions.

  These models are abstract structures.  They are *not* arithmetical theories,
  and their boxes are not arithmetised provability predicates.  Several of the
  finite models contain consistent theories that prove their own inconsistency
  statement `□ᵢ⊥` (`finite_countermodels_prove_own_inconsistency`); the ω-models
  `omegaChainFamily` and `omegaStarFamily` do not.
-/
import KernelTrust.Provability

namespace Toy.KernelTrust

/-- A pointed multi-relational Kripke model: a set of worlds, one accessibility
relation per theory index, and a base world (read: "the actual world"). -/
structure PointedKripke (ι : Type) where
  World : Type
  rel   : ι → World → World → Prop
  base  : World

namespace PointedKripke

variable {ι : Type}

/-- The family of theories read off from a pointed Kripke model.

Sentences are sets of worlds; `□ⱼA` holds at `w` when `A` holds at every
`relⱼ`-successor of `w`; and "theory `i` proves `A`" means `□ᵢA` holds at the
base world, i.e. `A` holds at every `relᵢ`-successor of the base world. -/
def toFamily (M : PointedKripke ι) : ProvFamily ι where
  Sent := M.World → Prop
  bot  := fun _ => False
  imp  := fun A B w => A w → B w
  box  := fun i A w => ∀ v, M.rel i w v → A v
  Thm  := fun i A => ∀ v, M.rel i M.base v → A v

/-- The GL frame condition for relation `i`: transitive and conversely
well-founded (no infinite ascending chain). -/
def GLFrame (M : PointedKripke ι) (i : ι) : Prop :=
  (∀ x y z, M.rel i x y → M.rel i y z → M.rel i x z) ∧
  WellFounded (fun y x => M.rel i x y)

/-- Every Kripke family is implicationally closed. -/
theorem toFamily_impClosed (M : PointedKripke ι) (i : ι) : M.toFamily.ImpClosed i :=
  ⟨fun hAB hA v hv => hAB v hv (hA v hv),
   fun _ _ _ _ a _ => a,
   fun _ _ _ _ _ f g a => f a (g a)⟩

/-- Every Kripke family has ex falso. -/
theorem toFamily_hasEfq (M : PointedKripke ι) (i : ι) : M.toFamily.HasEfq i :=
  fun _ _ _ h => h.elim

/-- Every Kripke family satisfies cross-distribution (boxes are normal). -/
theorem toFamily_crossDistrib (M : PointedKripke ι) (i j : ι) : M.toFamily.CrossDistrib i j :=
  fun _ _ _ _ hAB hA u hu => hAB u hu (hA u hu)

/-- On a GL frame, the Kripke family satisfies Löb's rule. -/
theorem toFamily_lobRule_of_glFrame (M : PointedKripke ι) (i : ι) (h : M.GLFrame i) :
    M.toFamily.LobRule i := by
  intro A hA v
  exact h.2.induction (C := fun v => M.rel i M.base v → A v) v
    (fun x ih hx => hA x hx (fun u hu => ih u hu (h.1 _ _ _ hx hu)))

end PointedKripke

/-! ## The constant model (used for examples) -/

/-- Two worlds `false → true`, the same relation for every index: "`ι` copies of
one consistent theory".  Every theory of this family proves `□ⱼA` for every
`j` and every `A` (`constFamily_proves_every_box`). -/
def constModel (ι : Type) : PointedKripke ι where
  World := Bool
  rel := fun _ x y => x = false ∧ y = true
  base := false

/-- The family of `constModel`. -/
abbrev constFamily (ι : Type) : ProvFamily ι := (constModel ι).toFamily

theorem constFamily_proves_every_box (ι : Type) (i j : ι) (A : (constFamily ι).Sent) :
    (constFamily ι).Thm i ((constFamily ι).box j A) := by
  intro v hv u hu
  have h1 := hv.2
  have h2 := hu.1
  rw [h1] at h2
  cases h2

theorem constFamily_lobRule (ι : Type) (i : ι) : (constFamily ι).LobRule i :=
  fun A hA v hv => hA v hv (constFamily_proves_every_box ι i i A v hv)

theorem constFamily_consistent (ι : Type) (i : ι) : (constFamily ι).Consistent i :=
  fun h => h true ⟨rfl, rfl⟩

theorem constFamily_not_proves_con (ι : Type) (i j : ι) :
    ¬ (constFamily ι).Thm i ((constFamily ι).con j) :=
  fun h => h true ⟨rfl, rfl⟩ (fun _ hu => by cases hu.1)

/-! ## K4b — the star model: a consistent ring of consistency proofs without `CrossSigma1` -/

/-- The star model on `n` theories: a base world `none` and one "tip" world
`some i` per theory; `relᵢ` relates every world other than `some i` to
`some i`.  For `n = 2` this is the three-world frame `{w, a, b}` with
`R₀ = {(w,a),(b,a)}` and `R₁ = {(w,b),(a,b)}`. -/
def starModel (n : Nat) : PointedKripke (Fin n) where
  World := Option (Fin n)
  rel := fun i x y => y = some i ∧ x ≠ some i
  base := none

/-- The family of `starModel`. -/
abbrev starFamily (n : Nat) : ProvFamily (Fin n) := (starModel n).toFamily

theorem starModel_glFrame (n : Nat) (i : Fin n) : (starModel n).GLFrame i :=
  ⟨fun _ _ _ hxy hyz => absurd hxy.1 hyz.2,
   ⟨fun a => Acc.intro a (fun y hy => Acc.intro y (fun _ hz => absurd hy.1 hz.2))⟩⟩

theorem starFamily_lobRule (n : Nat) (i : Fin n) : (starFamily n).LobRule i :=
  (starModel n).toFamily_lobRule_of_glFrame i (starModel_glFrame n i)

theorem starFamily_crossNec (n : Nat) (i j : Fin n) : (starFamily n).CrossNec i j := by
  intro A hA v _ u hu
  exact hA u ⟨hu.1, fun h => by cases h⟩

theorem starFamily_hbl (n : Nat) (i : Fin n) : (starFamily n).HBL i := by
  refine ⟨starFamily_crossNec n i i, (starModel n).toFamily_crossDistrib i i, ?_⟩
  intro A v hv _ u hu
  exact absurd hv.1 hu.2

theorem starFamily_consistent (n : Nat) (i : Fin n) : (starFamily n).Consistent i :=
  fun h => h (some i) ⟨rfl, fun h => by cases h⟩

theorem starFamily_ring {n : Nat} (hn : 2 ≤ n) (i : Fin n) :
    (starFamily n).Thm i ((starFamily n).con (ringNext i)) := by
  intro v hv hbox
  refine hbox (some (ringNext i)) ⟨rfl, ?_⟩
  rw [hv.1]
  intro e
  exact ringNext_ne_self hn i (Option.some.inj e).symm

theorem starFamily_not_crossSigma1 {n : Nat} (hn : 2 ≤ n) (i : Fin n) :
    ¬ (starFamily n).CrossSigma1 i (ringNext i) i := by
  intro h
  have h1 := h (fun _ => False) (some i) ⟨rfl, fun h => by cases h⟩
  refine h1 (fun u hu => hu.2 rfl) (some (ringNext i)) ⟨rfl, ?_⟩ (some i) ⟨rfl, ?_⟩
  · intro e
    exact ringNext_ne_self hn i (Option.some.inj e).symm
  · intro e
    exact ringNext_ne_self hn i (Option.some.inj e)

/-- **K4b (general `n`): a consistent ring without formalised Σ₁-completeness.**
For every `n ≥ 2`, the star family is a ring of `n` *consistent* theories, each
proving the consistency statement of its successor, in which every hypothesis
of K4a and K4a-local holds except the `CrossSigma1` component: every theory is
implicationally closed, satisfies `D1`–`D3`, Löb's rule and hence Gödel's second
incompleteness property, and cross-necessitation and cross-distribution hold
for all pairs.  `CrossSigma1 i (ringNext i) i` fails at *every* node. -/
theorem consistencyRing_consistent_without_crossSigma1 (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (starFamily n).ImpClosed i) ∧
    (∀ i, (starFamily n).HBL i) ∧
    (∀ i, (starFamily n).LobRule i) ∧
    (∀ i, (starFamily n).GodelII i) ∧
    (∀ i j, (starFamily n).CrossNec i j) ∧
    (∀ i j, (starFamily n).CrossDistrib i j) ∧
    (∀ i, (starFamily n).Thm i ((starFamily n).con (ringNext i))) ∧
    (∀ i, (starFamily n).Consistent i) ∧
    ¬ (∀ i, (starFamily n).Thm i (starFamily n).bot) ∧
    (∀ i, ¬ (starFamily n).CrossSigma1 i (ringNext i) i) :=
  ⟨(starModel n).toFamily_impClosed, starFamily_hbl n, starFamily_lobRule n,
   fun i => (starFamily_lobRule n i).godelII,
   starFamily_crossNec n, (starModel n).toFamily_crossDistrib, starFamily_ring hn,
   starFamily_consistent n,
   fun h => starFamily_consistent n ⟨0, by omega⟩ (h _),
   starFamily_not_crossSigma1 hn⟩

/-- **K4b.**  Two consistent theories that prove each other's consistency
statement exist once formalised Σ₁-completeness is dropped: in `starFamily 2`
both theories are consistent, theory 0 proves `con 1`, theory 1 proves `con 0`,
each theory is implicationally closed and satisfies `D1`–`D3` and Löb's rule,
cross-necessitation and cross-distribution hold for all pairs, and
`CrossSigma1` fails in *both* directions (`0 1 0` and `1 0 1`).  Breaking it in
one direction only would not suffice: see
`consistencyRing_anchor_inconsistent_of_impClosed_godelII_crossHBLFrom`. -/
theorem two_consistent_theories_prove_each_others_consistency_without_crossSigma1 :
    (starFamily 2).Consistent 0 ∧
    (starFamily 2).Consistent 1 ∧
    (starFamily 2).Thm 0 ((starFamily 2).con 1) ∧
    (starFamily 2).Thm 1 ((starFamily 2).con 0) ∧
    (∀ i, (starFamily 2).ImpClosed i) ∧
    (∀ i, (starFamily 2).HBL i) ∧
    (∀ i, (starFamily 2).LobRule i) ∧
    (∀ i j, (starFamily 2).CrossNec i j) ∧
    (∀ i j, (starFamily 2).CrossDistrib i j) ∧
    ¬ (starFamily 2).CrossSigma1 0 1 0 ∧
    ¬ (starFamily 2).CrossSigma1 1 0 1 :=
  ⟨starFamily_consistent 2 0, starFamily_consistent 2 1,
   starFamily_ring (Nat.le_refl 2) 0, starFamily_ring (Nat.le_refl 2) 1,
   (starModel 2).toFamily_impClosed, starFamily_hbl 2, starFamily_lobRule 2,
   starFamily_crossNec 2, (starModel 2).toFamily_crossDistrib,
   starFamily_not_crossSigma1 (Nat.le_refl 2) 0,
   starFamily_not_crossSigma1 (Nat.le_refl 2) 1⟩

/-- In the star model each theory, although consistent, proves its own
*inconsistency* statement `□ᵢ⊥`.  `omegaStarFamily` removes this defect. -/
theorem starFamily_proves_own_inconsistency (n : Nat) (i : Fin n) :
    (starFamily n).Thm i ((starFamily n).box i (starFamily n).bot) := by
  intro v hv u hu
  exact absurd hv.1 hu.2

/-! ## K4b without the own-inconsistency defect: the ω-star model -/

/-- The ω-star model on `n` theories: worlds are the base `none` and
`some (j, k)` for `k : Nat`; `relⱼ` leads from the base and from every world of
another theory to every `some (j, k)`, and from `some (j, m)` to `some (j, k)`
for `k < m`. -/
def omegaStarModel (n : Nat) : PointedKripke (Fin n) where
  World := Option (Fin n × Nat)
  rel := fun j x y =>
    (∃ k, y = some (j, k)) ∧
    match x with
    | none => True
    | some (i, m) => if i = j then (∃ k, y = some (j, k) ∧ k < m) else True
  base := none

/-- The family of `omegaStarModel`. -/
abbrev omegaStarFamily (n : Nat) : ProvFamily (Fin n) := (omegaStarModel n).toFamily

theorem omegaStarModel_glFrame (n : Nat) (i : Fin n) : (omegaStarModel n).GLFrame i := by
  constructor
  · intro x y z hxy hyz
    rcases hxy with ⟨⟨ky, rfl⟩, hxy2⟩
    rcases hyz with ⟨⟨kz, rfl⟩, hyz2⟩
    simp only [↓reduceIte] at hyz2
    rcases hyz2 with ⟨kz', hkz, hlt⟩
    cases hkz
    refine ⟨⟨kz, rfl⟩, ?_⟩
    cases x with
    | none => trivial
    | some p =>
      rcases p with ⟨ix, mx⟩
      by_cases hix : ix = i
      · simp only [hix, ↓reduceIte] at hxy2 ⊢
        rcases hxy2 with ⟨ky', hky, hlt2⟩
        cases hky
        exact ⟨kz, rfl, Nat.lt_trans hlt hlt2⟩
      · simp only [hix, ↓reduceIte]
  · refine ⟨fun x => ?_⟩
    have hacc_i : ∀ m : Nat, Acc (fun y x => (omegaStarModel n).rel i x y) (some (i, m)) := by
      intro m
      induction m using Nat.strongRecOn with
      | ind m ih =>
        refine Acc.intro (some (i, m)) (fun y hy => ?_)
        rcases hy with ⟨⟨ky, rfl⟩, hy2⟩
        simp only [↓reduceIte] at hy2
        rcases hy2 with ⟨ky', hky, hlt⟩
        cases hky
        exact ih ky hlt
    cases x with
    | none =>
      refine Acc.intro none (fun y hy => ?_)
      rcases hy with ⟨⟨ky, rfl⟩, _⟩
      exact hacc_i ky
    | some p =>
      rcases p with ⟨ix, mx⟩
      by_cases hix : ix = i
      · subst hix; exact hacc_i mx
      · refine Acc.intro (some (ix, mx)) (fun y hy => ?_)
        rcases hy with ⟨⟨ky, rfl⟩, _⟩
        exact hacc_i ky

theorem omegaStarFamily_crossNec (n : Nat) (i j : Fin n) : (omegaStarFamily n).CrossNec i j := by
  intro A hA v _ u hu
  rcases hu with ⟨⟨k, rfl⟩, _⟩
  exact hA (some (j, k)) ⟨⟨k, rfl⟩, trivial⟩

/-- **K4b without own-inconsistency proofs.**  For every `n ≥ 2`, the ω-star
family is a ring of `n` consistent theories, each proving the consistency
statement of its successor, in which every hypothesis of K4a and K4a-local
holds except `CrossSigma1`, and in which *no* theory proves its own
inconsistency statement `□ᵢ⊥`. -/
theorem consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency
    (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (omegaStarFamily n).ImpClosed i) ∧
    (∀ i, (omegaStarFamily n).HBL i) ∧
    (∀ i, (omegaStarFamily n).LobRule i) ∧
    (∀ i, (omegaStarFamily n).GodelII i) ∧
    (∀ i j, (omegaStarFamily n).CrossNec i j) ∧
    (∀ i j, (omegaStarFamily n).CrossDistrib i j) ∧
    (∀ i, (omegaStarFamily n).Thm i ((omegaStarFamily n).con (ringNext i))) ∧
    (∀ i, (omegaStarFamily n).Consistent i) ∧
    ¬ (∀ i, (omegaStarFamily n).Thm i (omegaStarFamily n).bot) ∧
    (∀ i, ¬ (omegaStarFamily n).Thm i ((omegaStarFamily n).box i (omegaStarFamily n).bot)) ∧
    (∀ i, ¬ (omegaStarFamily n).CrossSigma1 i (ringNext i) i) := by
  have hgl := omegaStarModel_glFrame n
  have hcons : ∀ i, (omegaStarFamily n).Consistent i :=
    fun i h => h (some (i, 0)) ⟨⟨0, rfl⟩, trivial⟩
  refine ⟨(omegaStarModel n).toFamily_impClosed,
          fun i => ⟨omegaStarFamily_crossNec n i i, (omegaStarModel n).toFamily_crossDistrib i i,
            fun A v hv hbox u hu z hz => hbox z ((hgl i).1 v u z hu hz)⟩,
          fun i => (omegaStarModel n).toFamily_lobRule_of_glFrame i (hgl i),
          fun i => ((omegaStarModel n).toFamily_lobRule_of_glFrame i (hgl i)).godelII,
          omegaStarFamily_crossNec n,
          (omegaStarModel n).toFamily_crossDistrib,
          ?_, hcons, fun h => hcons ⟨0, by omega⟩ (h _), ?_, ?_⟩
  · intro i v hv hbox
    rcases hv with ⟨⟨k, rfl⟩, _⟩
    refine hbox (some (ringNext i, 0)) ⟨⟨0, rfl⟩, ?_⟩
    have hne : i ≠ ringNext i := (ringNext_ne_self hn i).symm
    simp [hne]
  · intro i h
    exact h (some (i, 1)) ⟨⟨1, rfl⟩, trivial⟩ (some (i, 0))
      ⟨⟨0, rfl⟩, by simp only [↓reduceIte]; exact ⟨0, rfl, by decide⟩⟩
  · intro i hsig
    have h0 := hsig (fun _ => False) (some (i, 0)) ⟨⟨0, rfl⟩, trivial⟩
    have hbox0 : ∀ u, (omegaStarModel n).rel i (some (i, 0)) u → False := by
      intro u hu
      rcases hu with ⟨⟨k, rfl⟩, hu2⟩
      simp only [↓reduceIte] at hu2
      rcases hu2 with ⟨_, _, hlt⟩
      omega
    have h1 := h0 hbox0 (some (ringNext i, 0))
      ⟨⟨0, rfl⟩, by simp [(ringNext_ne_self hn i).symm]⟩
    exact h1 (some (i, 0)) ⟨⟨0, rfl⟩, by simp [ringNext_ne_self hn i]⟩

/-! ## Tightness of `CrossNec`: the leaf model -/

/-- Worlds of the leaf model: a base, one tip per theory, one leaf per theory. -/
inductive LeafWorld (n : Nat) : Type where
  | base : LeafWorld n
  | tip  : Fin n → LeafWorld n
  | leaf : Fin n → LeafWorld n

/-- The leaf model: `relⱼ` relates the base to `tip j`, and relates `tip i` to
`leaf i` whenever `j` is the ring successor of `i`.  For `n = 2` this is the
five-world frame `w →₀ a →₁ c`, `w →₁ b →₀ d`. -/
def leafModel (n : Nat) : PointedKripke (Fin n) where
  World := LeafWorld n
  rel := fun j x y =>
    (x = .base ∧ y = .tip j) ∨ (∃ i, ringNext i = j ∧ x = .tip i ∧ y = .leaf i)
  base := .base

/-- The family of `leafModel`. -/
abbrev leafFamily (n : Nat) : ProvFamily (Fin n) := (leafModel n).toFamily

theorem leafModel_rel_base {n : Nat} {j : Fin n} {v : LeafWorld n} :
    (leafModel n).rel j .base v ↔ v = .tip j := by
  constructor
  · rintro (⟨_, h⟩ | ⟨i, _, h, _⟩)
    · exact h
    · cases h
  · intro h
    exact .inl ⟨rfl, h⟩

theorem leafModel_rel_tip {n : Nat} {j i : Fin n} {u : LeafWorld n} :
    (leafModel n).rel j (.tip i) u ↔ ringNext i = j ∧ u = .leaf i := by
  constructor
  · rintro (⟨h, _⟩ | ⟨i', hn, hx, hy⟩)
    · cases h
    · cases hx
      exact ⟨hn, hy⟩
  · rintro ⟨h1, h2⟩
    exact .inr ⟨i, h1, rfl, h2⟩

theorem leafModel_rel_leaf {n : Nat} {j i : Fin n} {u : LeafWorld n} :
    ¬ (leafModel n).rel j (.leaf i) u := by
  rintro (⟨h, _⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem leafFamily_lobRule {n : Nat} (hn : 2 ≤ n) (i : Fin n) : (leafFamily n).LobRule i := by
  intro A hA v hv
  apply hA v hv
  intro u hu
  have hv' := leafModel_rel_base.mp hv
  subst hv'
  exact absurd (leafModel_rel_tip.mp hu).1 (ringNext_ne_self hn i)

theorem leafFamily_crossSigma1 (n : Nat) (i j k : Fin n) : (leafFamily n).CrossSigma1 i j k := by
  intro A v hv _ u hu z hz
  have hv' := leafModel_rel_base.mp hv
  subst hv'
  have hu' := (leafModel_rel_tip.mp hu).2
  subst hu'
  exact absurd hz leafModel_rel_leaf

theorem leafFamily_d1 {n : Nat} (hn : 2 ≤ n) (i : Fin n) : (leafFamily n).D1 i := by
  intro A _ v hv u hu
  have hv' := leafModel_rel_base.mp hv
  subst hv'
  exact absurd (leafModel_rel_tip.mp hu).1 (ringNext_ne_self hn i)

theorem leafFamily_ring (n : Nat) (i : Fin n) :
    (leafFamily n).Thm i ((leafFamily n).con (ringNext i)) := by
  intro v hv hbox
  have hv' := leafModel_rel_base.mp hv
  subst hv'
  exact hbox (.leaf i) (leafModel_rel_tip.mpr ⟨rfl, rfl⟩)

theorem leafFamily_consistent (n : Nat) (i : Fin n) : (leafFamily n).Consistent i :=
  fun h => h (.tip i) (leafModel_rel_base.mpr rfl)

theorem leafFamily_not_crossNec (n : Nat) (i : Fin n) :
    ¬ (leafFamily n).CrossNec i (ringNext i) := by
  intro h
  have h1 := h (fun x => x = .tip (ringNext i)) (fun v hv => leafModel_rel_base.mp hv)
    (.tip i) (leafModel_rel_base.mpr rfl) (.leaf i) (leafModel_rel_tip.mpr ⟨rfl, rfl⟩)
  cases h1

/-- **`CrossNec` is necessary for K4a and K4a-local.**  For every `n ≥ 2`, the
leaf family is a ring of `n` consistent theories, each proving the consistency
statement of its successor, in which every hypothesis holds except
cross-necessitation: implicational closure, `D1`–`D3`, Löb's rule and Gödel's
second incompleteness property for each theory, cross-distribution and
formalised Σ₁-completeness for all index combinations.  `CrossNec i (ringNext i)`
fails at every node. -/
theorem consistencyRing_consistent_without_crossNec (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (leafFamily n).ImpClosed i) ∧
    (∀ i, (leafFamily n).HBL i) ∧
    (∀ i, (leafFamily n).LobRule i) ∧
    (∀ i, (leafFamily n).GodelII i) ∧
    (∀ i j, (leafFamily n).CrossDistrib i j) ∧
    (∀ i j k, (leafFamily n).CrossSigma1 i j k) ∧
    (∀ i, (leafFamily n).Thm i ((leafFamily n).con (ringNext i))) ∧
    (∀ i, (leafFamily n).Consistent i) ∧
    ¬ (∀ i, (leafFamily n).Thm i (leafFamily n).bot) ∧
    (∀ i, ¬ (leafFamily n).CrossNec i (ringNext i)) :=
  ⟨(leafModel n).toFamily_impClosed,
   fun i => ⟨leafFamily_d1 hn i, (leafModel n).toFamily_crossDistrib i i,
     leafFamily_crossSigma1 n i i i⟩,
   leafFamily_lobRule hn, fun i => (leafFamily_lobRule hn i).godelII,
   (leafModel n).toFamily_crossDistrib, leafFamily_crossSigma1 n,
   leafFamily_ring n, leafFamily_consistent n,
   fun h => leafFamily_consistent n ⟨0, by omega⟩ (h _),
   leafFamily_not_crossNec n⟩

/-! ## Tightness of `CrossDistrib`: the possibility family (not a Kripke model) -/

/-- The possibility family on `n` theories.  Sentences are sets of indices;
theory `i` proves `A` when `A` holds at `i`; and `□ⱼA` holds at `w` when
`w = j` or `A` is *satisfiable*.  Away from its own point, each box behaves
like a possibility operator, so it does not distribute over implication. -/
def possibilityFamily (n : Nat) : ProvFamily (Fin n) where
  Sent := Fin n → Prop
  bot  := fun _ => False
  imp  := fun A B w => A w → B w
  box  := fun j A w => w = j ∨ ∃ u, A u
  Thm  := fun i A => A i

theorem possibilityFamily_impClosed (n : Nat) (i : Fin n) :
    (possibilityFamily n).ImpClosed i :=
  ⟨fun hAB hA => hAB hA, fun _ _ a _ => a, fun _ _ _ f g a => f a (g a)⟩

theorem possibilityFamily_lobRule (n : Nat) (i : Fin n) : (possibilityFamily n).LobRule i :=
  fun _ hA => hA (.inl rfl)

theorem possibilityFamily_crossNec (n : Nat) (i j : Fin n) :
    (possibilityFamily n).CrossNec i j :=
  fun _ hA => .inr ⟨j, hA⟩

theorem possibilityFamily_crossSigma1 (n : Nat) (i j k : Fin n) :
    (possibilityFamily n).CrossSigma1 i j k :=
  fun _ _ => .inr ⟨k, .inl rfl⟩

theorem possibilityFamily_hbl (n : Nat) (i : Fin n) : (possibilityFamily n).HBL i :=
  ⟨possibilityFamily_crossNec n i i, fun _ _ _ _ => .inl rfl,
   possibilityFamily_crossSigma1 n i i i⟩

theorem possibilityFamily_ring {n : Nat} (hn : 2 ≤ n) (i : Fin n) :
    (possibilityFamily n).Thm i ((possibilityFamily n).con (ringNext i)) := by
  rintro (h | ⟨_, hu⟩)
  · exact ringNext_ne_self hn i h.symm
  · exact hu

theorem possibilityFamily_consistent (n : Nat) (i : Fin n) :
    (possibilityFamily n).Consistent i :=
  fun h => h

theorem possibilityFamily_not_crossDistrib {n : Nat} (hn : 2 ≤ n) (i : Fin n) :
    ¬ (possibilityFamily n).CrossDistrib i (ringNext i) := by
  intro h
  have h1 := h (fun w => w = i) (fun _ => False)
    (.inr ⟨ringNext i, fun e => ringNext_ne_self hn i e⟩) (.inr ⟨i, rfl⟩)
  rcases h1 with e | ⟨_, hu⟩
  · exact ringNext_ne_self hn i e.symm
  · exact hu

/-- **`CrossDistrib` is necessary for K4a and K4a-local.**  For every `n ≥ 2`,
the possibility family is a ring of `n` consistent theories, each proving the
consistency statement of its successor, in which every hypothesis holds except
cross-distribution: implicational closure, `D1`–`D3`, Löb's rule and Gödel's
second incompleteness property for each theory, cross-necessitation and
formalised Σ₁-completeness for all index combinations.
`CrossDistrib i (ringNext i)` fails at every node.  (Kripke models cannot
serve here, because their boxes always distribute.) -/
theorem consistencyRing_consistent_without_crossDistrib (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (possibilityFamily n).ImpClosed i) ∧
    (∀ i, (possibilityFamily n).HBL i) ∧
    (∀ i, (possibilityFamily n).LobRule i) ∧
    (∀ i, (possibilityFamily n).GodelII i) ∧
    (∀ i j, (possibilityFamily n).CrossNec i j) ∧
    (∀ i j k, (possibilityFamily n).CrossSigma1 i j k) ∧
    (∀ i, (possibilityFamily n).Thm i ((possibilityFamily n).con (ringNext i))) ∧
    (∀ i, (possibilityFamily n).Consistent i) ∧
    ¬ (∀ i, (possibilityFamily n).Thm i (possibilityFamily n).bot) ∧
    (∀ i, ¬ (possibilityFamily n).CrossDistrib i (ringNext i)) :=
  ⟨possibilityFamily_impClosed n, possibilityFamily_hbl n, possibilityFamily_lobRule n,
   fun i => (possibilityFamily_lobRule n i).godelII,
   possibilityFamily_crossNec n, possibilityFamily_crossSigma1 n, possibilityFamily_ring hn,
   possibilityFamily_consistent n,
   fun h => possibilityFamily_consistent n ⟨0, by omega⟩ (h _),
   possibilityFamily_not_crossDistrib hn⟩

/-! ## Tightness of the Gödel II anchor: the reflexive point -/

/-- One reflexive world, the same relation for every index.  Here `□A` is just
`A`, so every theory proves every consistency statement and stays consistent. -/
def reflexiveModel (ι : Type) : PointedKripke ι where
  World := Unit
  rel := fun _ _ _ => True
  base := ()

/-- The family of `reflexiveModel`. -/
abbrev reflexiveFamily (ι : Type) : ProvFamily ι := (reflexiveModel ι).toFamily

theorem reflexiveFamily_crossHBL (ι : Type) : (reflexiveFamily ι).CrossHBL :=
  ⟨fun _ _ _ hA _ _ u _ => hA u trivial,
   fun i j => (reflexiveModel ι).toFamily_crossDistrib i j,
   fun _ _ _ _ _ _ hbox _ _ z _ => hbox z trivial⟩

theorem reflexiveFamily_proves_con (ι : Type) (i j : ι) :
    (reflexiveFamily ι).Thm i ((reflexiveFamily ι).con j) :=
  fun _ _ hbox => hbox () trivial

theorem reflexiveFamily_consistent (ι : Type) (i : ι) : (reflexiveFamily ι).Consistent i :=
  fun h => h () trivial

theorem reflexiveFamily_not_godelII (ι : Type) (i : ι) : ¬ (reflexiveFamily ι).GodelII i :=
  fun h => reflexiveFamily_consistent ι i (h (reflexiveFamily_proves_con ι i i))

theorem reflexiveFamily_not_lobRule (ι : Type) (i : ι) : ¬ (reflexiveFamily ι).LobRule i :=
  fun h => reflexiveFamily_not_godelII ι i h.godelII

/-- **The Gödel II anchor is necessary for K4a and K4a-local** (already for
`n = 1`).  In the reflexive family every other hypothesis holds: every theory
is implicationally closed, the full cross-theory conditions hold (hence
`D1`–`D3`), every theory proves every consistency statement, in particular its
ring successor's, and every theory is consistent.  Gödel's second
incompleteness property (hence Löb's rule) fails at *every* node. -/
theorem consistencyRing_consistent_without_godelII (n : Nat) (hn : 1 ≤ n) :
    (∀ i, (reflexiveFamily (Fin n)).ImpClosed i) ∧
    (reflexiveFamily (Fin n)).CrossHBL ∧
    (∀ i, (reflexiveFamily (Fin n)).Thm i ((reflexiveFamily (Fin n)).con (ringNext i))) ∧
    (∀ i, (reflexiveFamily (Fin n)).Consistent i) ∧
    ¬ (∀ i, (reflexiveFamily (Fin n)).Thm i (reflexiveFamily (Fin n)).bot) ∧
    (∀ i, ¬ (reflexiveFamily (Fin n)).GodelII i) ∧
    (∀ i, ¬ (reflexiveFamily (Fin n)).LobRule i) :=
  ⟨(reflexiveModel _).toFamily_impClosed, reflexiveFamily_crossHBL _,
   fun i => reflexiveFamily_proves_con _ i (ringNext i), reflexiveFamily_consistent _,
   fun h => reflexiveFamily_consistent _ ⟨0, hn⟩ (h _),
   reflexiveFamily_not_godelII _, reflexiveFamily_not_lobRule _⟩

/-! ## Positive control: an open chain of consistency proofs (ω-chain model) -/

/-- The ω-chain model on two theories.  Worlds are the base `none` and
`some k` for `k : Nat`.  From the base, `rel₁` reaches every `some k` and
`rel₀` reaches every `some (k+1)`; from `some m`, `rel₁` reaches `some k` for
`k < m` and `rel₀` reaches `some (k+1)` for `k + 1 < m`.  Theory 0 is the
"stronger" theory. -/
def omegaChainModel : PointedKripke (Fin 2) where
  World := Option Nat
  rel := fun i x y =>
    if i = 0 then
      (x = none ∧ ∃ k, y = some (k + 1)) ∨
      (∃ m k, x = some m ∧ y = some (k + 1) ∧ k + 1 < m)
    else
      (x = none ∧ ∃ k, y = some k) ∨
      (∃ m k, x = some m ∧ y = some k ∧ k < m)
  base := none

/-- The family of `omegaChainModel`. -/
abbrev omegaChainFamily : ProvFamily (Fin 2) := omegaChainModel.toFamily

private theorem omegaChain_wf :
    WellFounded (fun y x : Option Nat => ∃ i : Fin 2, omegaChainModel.rel i x y) := by
  have hacc_some : ∀ n : Nat,
      Acc (fun y x : Option Nat => ∃ i : Fin 2, omegaChainModel.rel i x y) (some n) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      refine Acc.intro (some n) (fun y hy => ?_)
      rcases hy with ⟨i, hi⟩
      by_cases hi0 : i = 0
      · simp only [omegaChainModel, hi0, ↓reduceIte] at hi
        rcases hi with ⟨hnone, _⟩ | ⟨m, k, hsm, hsk, hlt⟩
        · cases hnone
        · cases hsm; subst hsk; exact ih (k + 1) hlt
      · simp only [omegaChainModel, hi0, ↓reduceIte] at hi
        rcases hi with ⟨hnone, _⟩ | ⟨m, k, hsm, hsk, hlt⟩
        · cases hnone
        · cases hsm; subst hsk; exact ih k hlt
  refine ⟨fun x => ?_⟩
  cases x with
  | some n => exact hacc_some n
  | none =>
    refine Acc.intro none (fun y hy => ?_)
    rcases hy with ⟨i, hi⟩
    by_cases hi0 : i = 0
    · simp only [omegaChainModel, hi0, ↓reduceIte] at hi
      rcases hi with ⟨_, k, rfl⟩ | ⟨_, _, hnone, _, _⟩
      · exact hacc_some (k + 1)
      · cases hnone
    · simp only [omegaChainModel, hi0, ↓reduceIte] at hi
      rcases hi with ⟨_, k, rfl⟩ | ⟨_, _, hnone, _, _⟩
      · exact hacc_some k
      · cases hnone

theorem omegaChainModel_glFrame (i : Fin 2) : omegaChainModel.GLFrame i := by
  refine ⟨?_, Subrelation.wf (fun h => ⟨i, h⟩) omegaChain_wf⟩
  intro x y z hxy hyz
  by_cases hi0 : i = 0
  · simp only [omegaChainModel, hi0, ↓reduceIte] at hxy hyz ⊢
    rcases hxy with ⟨rfl, k1, rfl⟩ | ⟨m, k1, rfl, rfl, h1⟩
    · rcases hyz with ⟨hnone, _⟩ | ⟨_, k2, hsm, rfl, _⟩
      · cases hnone
      · exact .inl ⟨rfl, k2, rfl⟩
    · rcases hyz with ⟨hnone, _⟩ | ⟨_, k2, hsm, rfl, h2⟩
      · cases hnone
      · cases hsm; exact .inr ⟨m, k2, rfl, rfl, Nat.lt_trans h2 h1⟩
  · simp only [omegaChainModel, hi0, ↓reduceIte] at hxy hyz ⊢
    rcases hxy with ⟨rfl, k1, rfl⟩ | ⟨m, k1, rfl, rfl, h1⟩
    · rcases hyz with ⟨hnone, _⟩ | ⟨_, k2, hsm, rfl, _⟩
      · cases hnone
      · exact .inl ⟨rfl, k2, rfl⟩
    · rcases hyz with ⟨hnone, _⟩ | ⟨_, k2, hsm, rfl, h2⟩
      · cases hnone
      · cases hsm; exact .inr ⟨m, k2, rfl, rfl, Nat.lt_trans h2 h1⟩

theorem omegaChainFamily_lobRule (i : Fin 2) : omegaChainFamily.LobRule i :=
  omegaChainModel.toFamily_lobRule_of_glFrame i (omegaChainModel_glFrame i)

theorem omegaChainFamily_crossHBL : omegaChainFamily.CrossHBL := by
  refine ⟨?_, omegaChainModel.toFamily_crossDistrib, ?_⟩
  · intro i j A hA v _ u hu
    apply hA u
    by_cases hj0 : j = 0
    · simp only [omegaChainModel, hj0, ↓reduceIte] at hu ⊢
      rcases hu with ⟨_, k, rfl⟩ | ⟨_, k, _, rfl, _⟩
      · exact .inl ⟨trivial, k, rfl⟩
      · exact .inl ⟨trivial, k, rfl⟩
    · simp only [omegaChainModel, hj0, ↓reduceIte] at hu ⊢
      rcases hu with ⟨_, k, rfl⟩ | ⟨_, k, _, rfl, _⟩
      · exact .inl ⟨trivial, k, rfl⟩
      · exact .inl ⟨trivial, k, rfl⟩
  · intro i j k A v hv hbox u hu z hz
    apply hbox z
    have hrel_step : ∀ {p : Fin 2} {a b c : Option Nat},
        omegaChainModel.rel j a b → omegaChainModel.rel p b c →
        ∀ n, a = some n → omegaChainModel.rel p a c := by
      intro p a b c hab hbc n ha
      subst ha
      have hblt : ∃ r, b = some r ∧ r < n := by
        by_cases hj0 : j = 0
        · simp only [omegaChainModel, hj0, ↓reduceIte] at hab
          rcases hab with ⟨hnone, _⟩ | ⟨_, r, hsm, rfl, hlt⟩
          · cases hnone
          · cases hsm; exact ⟨r + 1, rfl, hlt⟩
        · simp only [omegaChainModel, hj0, ↓reduceIte] at hab
          rcases hab with ⟨hnone, _⟩ | ⟨_, r, hsm, rfl, hlt⟩
          · cases hnone
          · cases hsm; exact ⟨r, rfl, hlt⟩
      rcases hblt with ⟨r, rfl, hrn⟩
      by_cases hp0 : p = 0
      · simp only [omegaChainModel, hp0, ↓reduceIte] at hbc ⊢
        rcases hbc with ⟨hnone, _⟩ | ⟨_, s, hsr, rfl, hlt⟩
        · cases hnone
        · cases hsr; exact .inr ⟨n, s, rfl, rfl, Nat.lt_trans hlt hrn⟩
      · simp only [omegaChainModel, hp0, ↓reduceIte] at hbc ⊢
        rcases hbc with ⟨hnone, _⟩ | ⟨_, s, hsr, rfl, hlt⟩
        · cases hnone
        · cases hsr; exact .inr ⟨n, s, rfl, rfl, Nat.lt_trans hlt hrn⟩
    have hv_some : ∃ n, v = some n := by
      by_cases hi0 : i = 0
      · simp only [omegaChainModel, hi0, ↓reduceIte] at hv
        rcases hv with ⟨_, m, rfl⟩ | ⟨_, _, hnone, _, _⟩
        · exact ⟨m + 1, rfl⟩
        · cases hnone
      · simp only [omegaChainModel, hi0, ↓reduceIte] at hv
        rcases hv with ⟨_, m, rfl⟩ | ⟨_, _, hnone, _, _⟩
        · exact ⟨m, rfl⟩
        · cases hnone
    rcases hv_some with ⟨n, hn⟩
    exact hrel_step hu hz n hn

theorem omegaChainFamily_consistent : ∀ i, omegaChainFamily.Consistent i := by
  refine fin2_cases ?_ ?_
  · intro h; exact h (some 1) (.inl ⟨rfl, 0, rfl⟩)
  · intro h; exact h (some 0) (by simp [omegaChainModel])

theorem omegaChainFamily_proves_con_one : omegaChainFamily.Thm 0 (omegaChainFamily.con 1) := by
  intro v hv hbox
  simp only [omegaChainModel, ↓reduceIte] at hv
  rcases hv with ⟨_, k, rfl⟩ | ⟨_, _, hnone, _, _⟩
  · exact hbox (some 0) (by
      simp only [omegaChainModel, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
      exact .inr ⟨k + 1, 0, rfl, rfl, Nat.zero_lt_succ k⟩)
  · cases hnone

theorem omegaChainFamily_not_proves_con_zero :
    ¬ omegaChainFamily.Thm 1 (omegaChainFamily.con 0) := by
  intro h
  have h0 := h (some 0) (by simp [omegaChainModel])
  apply h0
  intro u hu
  simp only [omegaChainModel, ↓reduceIte] at hu
  rcases hu with ⟨hnone, _⟩ | ⟨_, k, hsm, _, hlt⟩
  · cases hnone
  · cases hsm; omega

private theorem omegaChain_base_step (i : Fin 2) : omegaChainModel.rel i none (some 3) := by
  by_cases hi0 : i = 0
  · simp only [omegaChainModel, hi0, ↓reduceIte]; exact .inl ⟨trivial, 2, rfl⟩
  · simp only [omegaChainModel, hi0, ↓reduceIte]; exact .inl ⟨trivial, 3, rfl⟩

private theorem omegaChain_step32 (j : Fin 2) : omegaChainModel.rel j (some 3) (some 2) := by
  by_cases hj0 : j = 0
  · simp only [omegaChainModel, hj0, ↓reduceIte]; exact .inr ⟨3, 1, rfl, rfl, by decide⟩
  · simp only [omegaChainModel, hj0, ↓reduceIte]; exact .inr ⟨3, 2, rfl, rfl, by decide⟩

private theorem omegaChain_step21 (k : Fin 2) : omegaChainModel.rel k (some 2) (some 1) := by
  by_cases hk0 : k = 0
  · simp only [omegaChainModel, hk0, ↓reduceIte]; exact .inr ⟨2, 0, rfl, rfl, by decide⟩
  · simp only [omegaChainModel, hk0, ↓reduceIte]; exact .inr ⟨2, 1, rfl, rfl, by decide⟩

/-- **K4a positive control (only closing the cycle is excluded).**  In the
ω-chain family every structural hypothesis of K4a holds (implicational
closure, Löb's rule and Gödel's second incompleteness property for both
theories, the full cross-theory conditions), both theories are consistent,
and theory 0 proves the consistency statement of theory 1.  Only the converse
consistency proof is missing, so the ring hypothesis fails.  No theory proves
any statement `□ⱼ⊥` or `□ⱼ□ₖ⊥`, so the cross-theory conditions hold
non-vacuously.  So K4a does not say that one theory cannot prove another's
consistency. -/
theorem consistency_proof_along_open_chain_is_consistent :
    (∀ i, omegaChainFamily.ImpClosed i) ∧
    (∀ i, omegaChainFamily.LobRule i) ∧
    (∀ i, omegaChainFamily.GodelII i) ∧
    omegaChainFamily.CrossHBL ∧
    (∀ i, omegaChainFamily.Consistent i) ∧
    omegaChainFamily.Thm 0 (omegaChainFamily.con 1) ∧
    ¬ omegaChainFamily.Thm 1 (omegaChainFamily.con 0) ∧
    ¬ (∀ i, omegaChainFamily.Thm i (omegaChainFamily.con (ringNext i))) ∧
    ¬ (∀ i, omegaChainFamily.Thm i omegaChainFamily.bot) ∧
    (∀ i j, ¬ omegaChainFamily.Thm i (omegaChainFamily.box j omegaChainFamily.bot)) ∧
    (∀ i j k, ¬ omegaChainFamily.Thm i
      (omegaChainFamily.box j (omegaChainFamily.box k omegaChainFamily.bot))) :=
  ⟨omegaChainModel.toFamily_impClosed, omegaChainFamily_lobRule,
   fun i => (omegaChainFamily_lobRule i).godelII,
   omegaChainFamily_crossHBL, omegaChainFamily_consistent,
   omegaChainFamily_proves_con_one, omegaChainFamily_not_proves_con_zero,
   fun h => omegaChainFamily_not_proves_con_zero (h 1),
   fun h => omegaChainFamily_consistent 0 (h 0),
   fun i j h => h (some 3) (omegaChain_base_step i) (some 2) (omegaChain_step32 j),
   fun i j k h => h (some 3) (omegaChain_base_step i) (some 2) (omegaChain_step32 j)
     (some 1) (omegaChain_step21 k)⟩

/-! ## Positive control: a ring with one unverified link -/

/-- A two-theory model in which theory 0 is inconsistent (it sees no world)
and theory 1 sees one dead-end world. -/
def oneBrokenNecModel : PointedKripke (Fin 2) where
  World := Bool
  rel := fun i x y => (i = 0 ∧ x = true ∧ y = true) ∨ (i = 1 ∧ x = false ∧ y = true)
  base := false

/-- The family of `oneBrokenNecModel`. -/
abbrev oneBrokenNecFamily : ProvFamily (Fin 2) := oneBrokenNecModel.toFamily

private theorem oneBrokenNec_thm0 (A : oneBrokenNecFamily.Sent) : oneBrokenNecFamily.Thm 0 A := by
  intro v hv
  rcases hv with ⟨_, hft, _⟩ | ⟨h01, _, _⟩
  · cases hft
  · cases h01

private theorem oneBrokenNec_crossSigma1 (i j k : Fin 2) : oneBrokenNecFamily.CrossSigma1 i j k := by
  intro A v hv hbox u hu z hz
  rcases hv with ⟨hi, hft, _⟩ | ⟨_, _, hvt⟩
  · cases hft
  · subst hvt
    rcases hu with ⟨_, _, hut⟩ | ⟨_, htf, _⟩
    · subst hut
      exact hbox z hz
    · cases htf

private theorem oneBrokenNec_crossNec01 : oneBrokenNecFamily.CrossNec 0 1 :=
  fun _ _ => oneBrokenNec_thm0 _

/-- **A ring with one unverified link (positive control for "every theory").**
On the two-theory ring, both theories prove each other's consistency
statement; theory 0 is an anchor in the sense of K4a-local (implicationally
closed, Löb's rule and Gödel's second incompleteness property, `CrossHBLFrom 0`)
and is inconsistent, as K4a-local requires; every other cross-theory condition
holds except the single ring link `CrossNec 1 0` (theory 1 does not verify
theory 0's proofs), and theory 1 is consistent.  Breaking one ring link
protects the theory before it from the anchor's inconsistency; it does not make
the anchor consistent. -/
theorem one_unverified_ring_link_leaves_anchor_inconsistent :
    (∀ i, oneBrokenNecFamily.ImpClosed i) ∧
    (∀ i, oneBrokenNecFamily.LobRule i) ∧
    (∀ i, oneBrokenNecFamily.GodelII i) ∧
    (∀ i j, oneBrokenNecFamily.CrossDistrib i j) ∧
    (∀ i j k, oneBrokenNecFamily.CrossSigma1 i j k) ∧
    oneBrokenNecFamily.D1 0 ∧
    oneBrokenNecFamily.D1 1 ∧
    oneBrokenNecFamily.CrossNec 0 1 ∧
    oneBrokenNecFamily.CrossHBLFrom 0 ∧
    (∀ i, oneBrokenNecFamily.Thm i (oneBrokenNecFamily.con (ringNext i))) ∧
    oneBrokenNecFamily.Thm 0 oneBrokenNecFamily.bot ∧
    oneBrokenNecFamily.Consistent 1 ∧
    ¬ oneBrokenNecFamily.CrossNec 1 0 := by
  have hLob : ∀ i, oneBrokenNecFamily.LobRule i := by
    refine fin2_cases ?_ ?_
    · intro A _; exact oneBrokenNec_thm0 A
    · intro A hA v hv
      apply hA v hv
      intro u hu
      rcases hv with ⟨h10, _, _⟩ | ⟨_, _, hvt⟩
      · cases h10
      · subst hvt
        rcases hu with ⟨h10, _, _⟩ | ⟨_, htf, _⟩
        · cases h10
        · cases htf
  refine ⟨oneBrokenNecModel.toFamily_impClosed, hLob, fun i => (hLob i).godelII,
          oneBrokenNecModel.toFamily_crossDistrib, oneBrokenNec_crossSigma1,
          fun A _ => oneBrokenNec_thm0 _, ?_, oneBrokenNec_crossNec01,
          ⟨fun j hj => ?_, fun j _ => oneBrokenNecModel.toFamily_crossDistrib 0 j,
            fun j k _ => oneBrokenNec_crossSigma1 0 j k⟩,
          ?_, oneBrokenNec_thm0 _, ?_, ?_⟩
  · intro A _ v hv u hu
    rcases hv with ⟨h10, _, _⟩ | ⟨_, _, hvt⟩
    · cases h10
    · subst hvt
      rcases hu with ⟨h10, _, _⟩ | ⟨_, htf, _⟩
      · cases h10
      · cases htf
  · match j, hj with
    | ⟨1, _⟩, _ => exact oneBrokenNec_crossNec01
  · refine fin2_cases ?_ ?_
    · exact oneBrokenNec_thm0 _
    · intro v hv hbox
      rcases hv with ⟨h10, _, _⟩ | ⟨_, _, hvt⟩
      · cases h10
      · subst hvt
        exact hbox true (.inl ⟨rfl, rfl, rfl⟩)
  · intro h
    exact h true (.inr ⟨rfl, rfl, rfl⟩)
  · intro hcn
    exact hcn oneBrokenNecFamily.bot (oneBrokenNec_thm0 _) true (.inr ⟨rfl, rfl, rfl⟩) true
      (.inl ⟨rfl, rfl, rfl⟩)

/-! ## Disclosure: consistent theories that prove their own inconsistency -/

/-- **Finite countermodels contain Σ₁-unsound theories.**  In the star, leaf
and possibility families (all `n ≥ 2`), every theory, although consistent,
proves its own inconsistency statement `□ᵢ⊥`; in the leaf and possibility
families every theory moreover proves every `□ⱼ□ₖ⊥`, so `CrossSigma1` holds
there vacuously; and in `oneBrokenNecFamily` the consistent theory 1 proves
`□₁⊥`.  These models establish independence of the named conditions, not the
existence of Σ₁-sound theories with the stated behaviour.  (The ω-models
`omegaChainFamily` and `omegaStarFamily` do not have this defect.) -/
theorem finite_countermodels_prove_own_inconsistency (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (starFamily n).Thm i ((starFamily n).box i (starFamily n).bot)) ∧
    (∀ i, (leafFamily n).Thm i ((leafFamily n).box i (leafFamily n).bot)) ∧
    (∀ i j k, (leafFamily n).Thm i
      ((leafFamily n).box j ((leafFamily n).box k (leafFamily n).bot))) ∧
    (∀ i, (possibilityFamily n).Thm i ((possibilityFamily n).box i (possibilityFamily n).bot)) ∧
    (∀ i j k, (possibilityFamily n).Thm i
      ((possibilityFamily n).box j ((possibilityFamily n).box k (possibilityFamily n).bot))) ∧
    oneBrokenNecFamily.Thm 1 (oneBrokenNecFamily.box 1 oneBrokenNecFamily.bot) := by
  refine ⟨starFamily_proves_own_inconsistency n, ?_, ?_, fun _ => .inl rfl,
    fun _ _ k => .inr ⟨k, .inl rfl⟩, ?_⟩
  · intro i v hv u hu
    have hv' := leafModel_rel_base.mp hv
    subst hv'
    exact absurd (leafModel_rel_tip.mp hu).1 (ringNext_ne_self hn i)
  · intro i j k v hv u hu z hz
    have hv' := leafModel_rel_base.mp hv
    subst hv'
    have hu' := (leafModel_rel_tip.mp hu).2
    subst hu'
    exact absurd hz leafModel_rel_leaf
  · intro v hv u hu
    rcases hv with ⟨h10, _, _⟩ | ⟨_, _, hvt⟩
    · cases h10
    · subst hvt
      rcases hu with ⟨h10, _, _⟩ | ⟨_, htf, _⟩
      · cases h10
      · cases htf

/-! ## K5 / K5-iff tightness witnesses and the consistent K5-iff instance -/

/-- **K5 without inconsistency.**  Theory 0 of the ω-chain family is closed
under modus ponens and ex falso and is consistent, and it proves neither its
own local reflection schema nor its own consistency statement. -/
theorem local_reflection_fails_without_inconsistency :
    omegaChainFamily.MpClosed 0 ∧
    omegaChainFamily.HasEfq 0 ∧
    omegaChainFamily.Consistent 0 ∧
    ¬ (∀ (j : Fin 2) (A : omegaChainFamily.Sent),
        omegaChainFamily.Thm 0 (omegaChainFamily.imp (omegaChainFamily.box j A) A)) ∧
    ¬ (∀ j : Fin 2, omegaChainFamily.Thm 0 (omegaChainFamily.con j)) := by
  have hcons := omegaChainFamily_consistent 0
  have hncon : ¬ omegaChainFamily.Thm 0 (omegaChainFamily.con 0) :=
    fun h => hcons ((omegaChainFamily_lobRule 0).godelII h)
  exact ⟨(omegaChainModel.toFamily_impClosed 0).mp, omegaChainModel.toFamily_hasEfq 0, hcons,
    fun h => hncon (h 0 _), fun h => hncon (h 0)⟩

/-- **K5-iff non-vacuity (consistent instance).**  Theory 0 of the ω-chain
family satisfies every hypothesis of K5-iff and is consistent, so both sides
of the equivalence are false there. -/
theorem k5_iff_nonvacuous_consistent :
    omegaChainFamily.MpClosed 0 ∧
    omegaChainFamily.HasEfq 0 ∧
    omegaChainFamily.GodelII 0 ∧
    omegaChainFamily.Consistent 0 ∧
    ¬ (∀ A : omegaChainFamily.Sent,
        omegaChainFamily.Thm 0 (omegaChainFamily.imp (omegaChainFamily.box 0 A) A)) :=
  ⟨(omegaChainModel.toFamily_impClosed 0).mp, omegaChainModel.toFamily_hasEfq 0,
   (omegaChainFamily_lobRule 0).godelII, omegaChainFamily_consistent 0,
   fun h => omegaChainFamily_consistent 0 ((omegaChainFamily_lobRule 0).godelII (h _))⟩

/-- **K5-iff without Gödel II.**  The reflexive theory is closed under modus
ponens and ex falso and is consistent, Gödel's second incompleteness property
fails, the theory proves its own local reflection schema, and the equivalence
of K5-iff fails. -/
theorem local_reflection_iff_fails_without_godelII :
    (reflexiveFamily Unit).MpClosed () ∧
    (reflexiveFamily Unit).HasEfq () ∧
    (reflexiveFamily Unit).Consistent () ∧
    ¬ (reflexiveFamily Unit).GodelII () ∧
    (∀ A : (reflexiveFamily Unit).Sent,
        (reflexiveFamily Unit).Thm () ((reflexiveFamily Unit).imp ((reflexiveFamily Unit).box () A) A)) ∧
    ¬ ((∀ A : (reflexiveFamily Unit).Sent,
          (reflexiveFamily Unit).Thm ()
            ((reflexiveFamily Unit).imp ((reflexiveFamily Unit).box () A) A)) ↔
        (reflexiveFamily Unit).Thm () (reflexiveFamily Unit).bot) := by
  have hrefl : ∀ A : (reflexiveFamily Unit).Sent,
      (reflexiveFamily Unit).Thm () ((reflexiveFamily Unit).imp ((reflexiveFamily Unit).box () A) A) :=
    fun _ v _ hbox => hbox v trivial
  exact ⟨((reflexiveModel Unit).toFamily_impClosed ()).mp, (reflexiveModel Unit).toFamily_hasEfq (),
    reflexiveFamily_consistent Unit (), reflexiveFamily_not_godelII Unit (), hrefl,
    fun h => reflexiveFamily_consistent Unit () (h.mp hrefl)⟩

/-! ## Examples for the provability-interface definitions -/

/-- The empty theory family: one sentence, and no theory proves anything. -/
def emptyFamily (ι : Type) : ProvFamily ι where
  Sent := Unit
  bot := ()
  imp := fun _ _ => ()
  box := fun _ _ => ()
  Thm := fun _ _ => False

/-- Positive example (`ProvFamily.Consistent`). -/
theorem ex_consistent_pos : (constFamily Unit).Consistent () := constFamily_consistent _ _

/-- Negative example (`ProvFamily.Consistent`). -/
theorem ex_consistent_neg : ¬ (trivialFamily Unit).Consistent () := fun h => h trivial

/-- Positive example (`ProvFamily.con`): the reflexive theory proves its own
consistency statement. -/
theorem ex_con_pos : (reflexiveFamily Unit).Thm () ((reflexiveFamily Unit).con ()) :=
  reflexiveFamily_proves_con _ _ _

/-- Negative example (`ProvFamily.con`): the constant theory does not. -/
theorem ex_con_neg : ¬ (constFamily Unit).Thm () ((constFamily Unit).con ()) :=
  constFamily_not_proves_con _ _ _

/-- Positive example (`ImpClosed`, `MpClosed`): every Kripke family. -/
theorem ex_impClosed_pos : (constFamily Unit).ImpClosed () :=
  (constModel Unit).toFamily_impClosed ()

/-- Negative example (`ImpClosed`): the empty theory proves no axiom. -/
theorem ex_impClosed_neg : ¬ (emptyFamily Unit).ImpClosed () := fun h => h.axK () ()

/-- Positive example (`HasEfq`): every Kripke family. -/
theorem ex_hasEfq_pos : (constFamily Unit).HasEfq () := (constModel Unit).toFamily_hasEfq ()

/-- Negative example (`HasEfq`): the empty theory. -/
theorem ex_hasEfq_neg : ¬ (emptyFamily Unit).HasEfq () := fun h => h ()

/-- Positive example (`D1`, `D2`, `D3`, `HBL`): each theory of the star family. -/
theorem ex_hbl_pos : (starFamily 2).HBL 0 := starFamily_hbl 2 0

/-- Negative example (`D1`): in the one-theory leaf model `base → tip → leaf`
(a non-transitive frame) the theory proves `A := {tip}` but not `□A`. -/
theorem ex_d1_neg : ¬ (leafFamily 1).D1 0 := leafFamily_not_crossNec 1 0

/-- Negative example (`D2`, `D3`, `HBL`): the empty theory. -/
theorem ex_hbl_neg :
    ¬ (emptyFamily Unit).D2 () ∧ ¬ (emptyFamily Unit).D3 () ∧ ¬ (emptyFamily Unit).HBL () :=
  ⟨fun h => h () (), fun h => h (), fun h => h.d3 ()⟩

/-- Positive example (`LobRule`). -/
theorem ex_lobRule_pos : (starFamily 2).LobRule 0 := starFamily_lobRule 2 0

/-- Negative example (`LobRule`). -/
theorem ex_lobRule_neg : ¬ (reflexiveFamily Unit).LobRule () := reflexiveFamily_not_lobRule _ _

/-- Positive example (`GodelII`): theory 0 of the ω-chain family, which is
consistent and Σ₁-sound in the sense that it proves no `□ⱼ⊥`. -/
theorem ex_godelII_pos : omegaChainFamily.GodelII 0 := (omegaChainFamily_lobRule 0).godelII

/-- Negative example (`GodelII`): the reflexive theory proves its own
consistency statement and is consistent. -/
theorem ex_godelII_neg : ¬ (reflexiveFamily Unit).GodelII () := reflexiveFamily_not_godelII _ _

/-- Positive example (`CrossNec`). -/
theorem ex_crossNec_pos : (starFamily 2).CrossNec 0 1 := starFamily_crossNec 2 0 1

/-- Negative example (`CrossNec`). -/
theorem ex_crossNec_neg : ¬ (leafFamily 2).CrossNec 0 1 := leafFamily_not_crossNec 2 0

/-- Positive example (`CrossDistrib`). -/
theorem ex_crossDistrib_pos : (starFamily 2).CrossDistrib 0 1 :=
  (starModel 2).toFamily_crossDistrib 0 1

/-- Negative example (`CrossDistrib`). -/
theorem ex_crossDistrib_neg : ¬ (possibilityFamily 2).CrossDistrib 0 1 :=
  possibilityFamily_not_crossDistrib (Nat.le_refl 2) 0

/-- Positive example (`CrossSigma1`), non-vacuous: in the ω-chain family no
theory proves any `□ⱼ□ₖ⊥`. -/
theorem ex_crossSigma1_pos : omegaChainFamily.CrossSigma1 0 1 0 :=
  omegaChainFamily_crossHBL.sigma1 0 1 0

/-- Negative example (`CrossSigma1`). -/
theorem ex_crossSigma1_neg : ¬ (starFamily 2).CrossSigma1 0 1 0 :=
  starFamily_not_crossSigma1 (Nat.le_refl 2) 0

/-- Positive example (`CrossHBL`), non-vacuous: the ω-chain family. -/
theorem ex_crossHBL_pos : omegaChainFamily.CrossHBL := omegaChainFamily_crossHBL

/-- Negative example (`CrossHBL`). -/
theorem ex_crossHBL_neg : ¬ (starFamily 2).CrossHBL :=
  fun h => starFamily_not_crossSigma1 (Nat.le_refl 2) 0 (h.sigma1 0 1 0)

/-- Positive example (`CrossHBLFrom`), strictly weaker than `CrossHBL`:
theory 0 of `oneBrokenNecFamily` satisfies the conditions towards theory 1,
while `CrossHBL` fails for the family. -/
theorem ex_crossHBLFrom_pos :
    oneBrokenNecFamily.CrossHBLFrom 0 ∧ ¬ oneBrokenNecFamily.CrossHBL :=
  ⟨one_unverified_ring_link_leaves_anchor_inconsistent.2.2.2.2.2.2.2.2.1,
   fun h => one_unverified_ring_link_leaves_anchor_inconsistent.2.2.2.2.2.2.2.2.2.2.2.2
     (h.nec 1 0)⟩

/-- Negative example (`CrossHBLFrom`). -/
theorem ex_crossHBLFrom_neg : ¬ (starFamily 2).CrossHBLFrom 0 :=
  fun h => starFamily_not_crossSigma1 (Nat.le_refl 2) 0 (h.sigma1 1 0 (by decide))

/-- Positive example (`PointedKripke.GLFrame`). -/
theorem ex_glFrame_pos : (starModel 2).GLFrame 0 := starModel_glFrame 2 0

/-- Negative example (`PointedKripke.GLFrame`): a reflexive point is not
conversely well-founded. -/
theorem ex_glFrame_neg : ¬ (reflexiveModel Unit).GLFrame () :=
  fun h => reflexiveFamily_not_lobRule Unit () ((reflexiveModel Unit).toFamily_lobRule_of_glFrame () h)

/-- Positive example (`PointedKripke.toFamily`): in the star family, "theory `i`
proves `A`" is truth of `A` at the tip `some i`. -/
theorem ex_toFamily_pos (n : Nat) (i : Fin n) (A : Option (Fin n) → Prop) :
    (starFamily n).Thm i A ↔ A (some i) :=
  ⟨fun h => h (some i) ⟨rfl, fun h => by cases h⟩, fun h v hv => by rw [hv.1]; exact h⟩

/-- Negative example (`PointedKripke.toFamily`): truth at the base world is
*not* theoremhood; `A := {base}` is true at the base and proved by no theory of
the star family. -/
theorem ex_toFamily_neg (n : Nat) (i : Fin n) :
    ¬ (starFamily n).Thm i (fun w => w = none) :=
  fun h => by cases h (some i) ⟨rfl, fun h => by cases h⟩

/-- **K4a-local in a mixed ring.**  In `oneBrokenNecFamily` (`n = 2`), theory
`0` satisfies every hypothesis of K4a-local (implicational closure, Gödel's
second incompleteness property, the cross-theory conditions towards theory `1`,
and the ring hypothesis), while theory `1` of the same ring is consistent. -/
theorem k4a_local_hypotheses_hold_in_mixed_ring :
    oneBrokenNecFamily.ImpClosed 0 ∧
    oneBrokenNecFamily.GodelII 0 ∧
    oneBrokenNecFamily.CrossHBLFrom 0 ∧
    (∀ i, oneBrokenNecFamily.Thm i (oneBrokenNecFamily.con (ringNext i))) ∧
    oneBrokenNecFamily.Consistent 1 := by
  have h := one_unverified_ring_link_leaves_anchor_inconsistent
  exact ⟨h.1 0, h.2.2.1 0, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- In `omegaStarFamily n`, no theory proves any nested `□ⱼ□ₖ⊥`. -/
theorem omegaStarFamily_not_proves_nested_box_bot (n : Nat) (i j k : Fin n) :
    ¬ (omegaStarFamily n).Thm i
        ((omegaStarFamily n).box j ((omegaStarFamily n).box k (omegaStarFamily n).bot)) := by
  intro h
  have hi : (omegaStarModel n).rel i none (some (i, 2)) := ⟨⟨2, rfl⟩, trivial⟩
  by_cases hij : i = j
  · subst hij
    have hj : (omegaStarModel n).rel i (some (i, 2)) (some (i, 1)) :=
      ⟨⟨1, rfl⟩, by simp only [↓reduceIte]; exact ⟨1, rfl, by decide⟩⟩
    by_cases hik : i = k
    · subst hik
      exact h (some (i, 2)) hi (some (i, 1)) hj (some (i, 0))
        ⟨⟨0, rfl⟩, by simp only [↓reduceIte]; exact ⟨0, rfl, by decide⟩⟩
    · exact h (some (i, 2)) hi (some (i, 1)) hj (some (k, 0))
        ⟨⟨0, rfl⟩, by simp [hik]⟩
  · have hj : (omegaStarModel n).rel j (some (i, 2)) (some (j, 1)) :=
      ⟨⟨1, rfl⟩, by simp [hij]⟩
    by_cases hjk : j = k
    · subst hjk
      exact h (some (i, 2)) hi (some (j, 1)) hj (some (j, 0))
        ⟨⟨0, rfl⟩, by simp only [↓reduceIte]; exact ⟨0, rfl, by decide⟩⟩
    · exact h (some (i, 2)) hi (some (j, 1)) hj (some (k, 0))
        ⟨⟨0, rfl⟩, by simp [hjk]⟩

/-- **`2 ≤ n` is needed in the general-`n` K4b statements.**  For `n = 1` the
ring successor of theory `0` is theory `0` itself, and neither `starFamily 1`
nor `omegaStarFamily 1` proves its own consistency statement, so the ring
conjunct of `consistencyRing_consistent_without_crossSigma1` and of
`consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency`
fails at `n = 1`.  For `n = 0` there is no theory, so their conjunct
`¬ ∀ i, Thm i ⊥` fails. -/
theorem consistencyRing_consistent_without_crossSigma1_fails_below_two :
    ringNext (0 : Fin 1) = 0 ∧
    ¬ (∀ i, (starFamily 1).Thm i ((starFamily 1).con (ringNext i))) ∧
    ¬ (∀ i, (omegaStarFamily 1).Thm i ((omegaStarFamily 1).con (ringNext i))) ∧
    (∀ i, (starFamily 0).Thm i (starFamily 0).bot) ∧
    (∀ i, (omegaStarFamily 0).Thm i (omegaStarFamily 0).bot) := by
  have hr : ringNext (0 : Fin 1) = 0 := rfl
  refine ⟨hr, fun h => ?_, fun h => ?_, fun i => i.elim0, fun i => i.elim0⟩
  · exact h 0 (some 0) ⟨rfl, fun e => by cases e⟩ (fun v hv => hv.2 (by rw [hr]))
  · refine h 0 (some (0, 0)) ⟨⟨0, rfl⟩, trivial⟩ (fun v hv => ?_)
    rcases hv with ⟨_, hv2⟩
    rw [hr] at hv2
    simp only [↓reduceIte] at hv2
    rcases hv2 with ⟨_, _, hlt⟩
    exact Nat.not_lt_zero _ hlt

end Toy.KernelTrust
