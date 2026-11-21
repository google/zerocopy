import ToyDataflow.Examples

/-!
# Further witnesses for the exactness theorems

Non-vacuity and canonical counterexamples for the two corollaries
(`..._of_allReachable`, `..._of_strict`), for the existence form, and for the
gen/kill form.
-/

namespace Toy.Dataflow

/-- A gen/kill loop all of whose transfers are strict (empty gen sets). -/
def strictLoopGK : CFG 2 (Fin 2 → Bool) where
  edges := [(0, 1), (1, 1)]
  entry := 0
  init := fun _ => true
  f := fun u => genKill (fun _ => false) (fun i => decide (u = 1 ∧ i = 0))

def strictLoopGKSol : Fin 2 → Fin 2 → Bool := fun _ _ => true

/-- Non-vacuity of the strict corollary: every hypothesis holds, including
`∀ u, Strict`. -/
theorem strict_exactness_nonvacuous :
    (bvLat 2).IsJSL ∧ (bvLat 2).AscendingChainCondition ∧
      (∀ u, Distributive (bvLat 2) (strictLoopGK.f u)) ∧
      (∀ u, Strict (bvLat 2) (strictLoopGK.f u)) ∧
      AllReachable strictLoopGK ∧
      IsLeastSolution (bvLat 2) strictLoopGK strictLoopGKSol := by
  refine ⟨bvLat_isJSL 2, bvLat_acc 2, fun _ => genKill_distributive _ _,
    fun _ => (genKill_strict_iff _ _).2 rfl, ?_, ⟨⟨by decide, by decide⟩, ?_⟩⟩
  · intro v
    have e01 : ((0 : Fin 2), (1 : Fin 2)) ∈ strictLoopGK.edges := by decide
    have hv : v = 0 ∨ v = 1 := by revert v; decide
    rcases hv with rfl | rfl
    · exact ⟨.nil⟩
    · exact ⟨.snoc .nil e01⟩
  · intro y hy v i hi
    have hy0 := hy.1 i rfl
    have hy1 := hy.2 0 1 (by decide) i (by simp [strictLoopGK, genKill]; exact hy0)
    have hv : ∀ v : Fin 2, v = 0 ∨ v = 1 := by decide
    rcases hv v with rfl | rfl
    · exact hy0
    · exact hy1

/-- A CFG where `UnreachableStrict` holds but neither `AllReachable` nor
`∀ u, Strict`: node 2 is unreachable (with empty gen), while node 0 is non-strict
(gen `{0}`). -/
def midStrictCFG : CFG 3 (Fin 1 → Bool) where
  edges := [(0, 1)]
  entry := 0
  init := fun _ => false
  f := fun u => genKill (fun _ => decide (u = 0)) (fun _ => false)

def midStrictSol : Fin 3 → Fin 1 → Bool := fun v _ => decide (v = 1)

/-- Non-vacuity of the main exactness theorem in a case covered by neither
corollary. -/
theorem unreachableStrict_strictly_between_nonvacuous :
    (bvLat 1).IsJSL ∧ (bvLat 1).AscendingChainCondition ∧
      (∀ u, Distributive (bvLat 1) (midStrictCFG.f u)) ∧
      UnreachableStrict (bvLat 1) midStrictCFG ∧
      ¬ AllReachable midStrictCFG ∧
      ¬ (∀ u, Strict (bvLat 1) (midStrictCFG.f u)) ∧
      IsLeastSolution (bvLat 1) midStrictCFG midStrictSol := by
  have hnr2 : ¬ Reachable midStrictCFG 2 := by
    rw [reachable_iff_exists_pathVals]
    rintro ⟨b, hb⟩
    rw [pathVals_iff] at hb
    rcases hb with ⟨h, _⟩ | ⟨u, a, hu, _, _⟩
    · exact absurd h (by decide)
    · have : ∀ u : Fin 3, (u, (2 : Fin 3)) ∉ midStrictCFG.edges := by decide
      exact absurd hu (this u)
  refine ⟨bvLat_isJSL 1, bvLat_acc 1, fun _ => genKill_distributive _ _, ?_,
    fun h => hnr2 (h 2), fun h => ?_, ⟨⟨by decide, by decide⟩, ?_⟩⟩
  · intro u hu
    have hu' : ∀ u : Fin 3, u = 0 ∨ u = 1 ∨ u = 2 := by decide
    have hu2 : u = 2 := by
      rcases hu' u with rfl | rfl | rfl
      · exact absurd ⟨.nil⟩ hu
      · exact absurd ⟨.snoc .nil (by decide)⟩ hu
      · rfl
    subst hu2
    exact (genKill_strict_iff (fun _ => decide ((2 : Fin 3) = 0)) (fun _ => false)).2 rfl
  · have := congrFun (h 0) 0
    simp [midStrictCFG, genKill, bvLat] at this
  · intro y hy v i hi
    have hv : v = 1 := by simpa [midStrictSol] using hi
    subst hv
    exact hy.2 0 1 (by decide) i (by simp [midStrictCFG, genKill])

def OmegaTwo.succStrict : OmegaTwo → OmegaTwo
  | .fin 0 => .fin 0
  | .fin (k + 1) => .fin (k + 2)
  | .omega => .omega1
  | .omega1 => .omega1

theorem omega_succStrict_distributive : Distributive omegaLat OmegaTwo.succStrict := by
  intro a b
  cases a with
  | fin ka =>
    cases ka with
    | zero => cases b with
      | fin kb => cases kb <;> simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
      | omega => simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
      | omega1 => simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
    | succ ka => cases b with
      | fin kb => cases kb <;> simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict] <;> omega
      | omega => simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
      | omega1 => simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
  | omega => cases b with
    | fin kb => cases kb <;> simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
    | omega => simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
    | omega1 => simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
  | omega1 => cases b with
    | fin kb => cases kb <;> simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
    | omega => simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]
    | omega1 => simp [omegaLat, OmegaTwo.join, OmegaTwo.succStrict]

def omegaStrictCFG : CFG 2 OmegaTwo where
  edges := [(0, 1), (1, 1)]
  entry := 0
  init := .fin 1
  f := fun u => if u = 1 then OmegaTwo.succStrict else id

def omegaStrictSol : Fin 2 → OmegaTwo := fun v => if v = 1 then .omega1 else .fin 1

theorem omegaStrictCFG_walk_val_fin {v : Fin 2} (p : Walk omegaStrictCFG v) :
    ∃ k, p.val = .fin (k + 1) := by
  induction p with
  | nil => exact ⟨0, rfl⟩
  | @snoc u w p _ ih =>
    obtain ⟨k, hk⟩ := ih
    by_cases hu : u = 1
    · refine ⟨k + 1, ?_⟩
      show omegaStrictCFG.f u p.val = _
      rw [hk]; simp [omegaStrictCFG, hu, OmegaTwo.succStrict]
    · refine ⟨k, ?_⟩
      show omegaStrictCFG.f u p.val = _
      rw [hk]; simp [omegaStrictCFG, hu]

theorem omegaStrictCFG_pathVals_one (k : Nat) : pathVals omegaStrictCFG 1 (.fin (k + 1)) := by
  induction k with
  | zero => exact pathVals_step (u := 0) (by decide) (pathVals_init omegaStrictCFG)
  | succ k ih => exact pathVals_step (u := 1) (by decide) ih

/-- Counterexample (exactness without the ascending chain condition, all transfers
strict): on `ℕ ∪ {ω, ω+1}` with a loop whose transfer is a strict variant of the
successor, the least solution at node 1 is `ω + 1` while MOP there is `ω`. -/
theorem strict_exactness_needs_acc :
    omegaLat.IsJSL ∧ ¬ omegaLat.AscendingChainCondition ∧
      (∀ u, Distributive omegaLat (omegaStrictCFG.f u)) ∧
      (∀ u, Strict omegaLat (omegaStrictCFG.f u)) ∧
      AllReachable omegaStrictCFG ∧
      IsLeastSolution omegaLat omegaStrictCFG omegaStrictSol ∧
      IsMOPAt omegaLat omegaStrictCFG 1 .omega ∧
      ¬ IsMOPAt omegaLat omegaStrictCFG 1 (omegaStrictSol 1) := by
  have hdist : ∀ u, Distributive omegaLat (omegaStrictCFG.f u) := by
    intro u
    by_cases hu : u = 1
    · have e : omegaStrictCFG.f u = OmegaTwo.succStrict := by simp [omegaStrictCFG, hu]
      rw [e]; exact omega_succStrict_distributive
    · have e : omegaStrictCFG.f u = id := by simp [omegaStrictCFG, hu]
      rw [e]; exact fun _ _ => rfl
  have hstrict : ∀ u, Strict omegaLat (omegaStrictCFG.f u) := by
    intro u
    by_cases hu : u = 1 <;> simp [Strict, omegaLat, omegaStrictCFG, hu, OmegaTwo.succStrict]
  have hall : AllReachable omegaStrictCFG := by
    intro v
    have hv : v = 0 ∨ v = 1 := by revert v; decide
    rcases hv with rfl | rfl
    · exact ⟨.nil⟩
    · exact ⟨.snoc .nil (by decide)⟩
  have hleast : IsLeastSolution omegaLat omegaStrictCFG omegaStrictSol := by
    refine ⟨⟨by simp [omegaLat, OmegaTwo.le, omegaStrictCFG, omegaStrictSol], ?_⟩, ?_⟩
    · intro u w huw
      simp only [omegaStrictCFG, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at huw
      rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
      · simp [omegaLat, OmegaTwo.le, omegaStrictSol, omegaStrictCFG]
      · simp [omegaLat, OmegaTwo.le, omegaStrictSol, omegaStrictCFG, OmegaTwo.succStrict]
      · exact h.elim
    · intro y hy v
      have h01 := hy.2 0 1 (by decide)
      have h11 := hy.2 1 1 (by decide)
      have hy0 : OmegaTwo.le (.fin 1) (y 0) := hy.1
      have hy1_ge1 : OmegaTwo.le (.fin 1) (y 1) :=
        omegaLat_isJSL.trans _ _ _ hy0 (by simpa [omegaStrictCFG] using h01)
      have hy1 : y 1 = .omega1 := by
        cases hy1v : y 1 with
        | fin m =>
          cases m with
          | zero => simp [OmegaTwo.le, hy1v] at hy1_ge1
          | succ m =>
            simp [omegaStrictCFG, hy1v, omegaLat, OmegaTwo.le, OmegaTwo.succStrict] at h11
        | omega => simp [omegaStrictCFG, hy1v, omegaLat, OmegaTwo.le, OmegaTwo.succStrict] at h11
        | omega1 => rfl
      have hv : v = 0 ∨ v = 1 := by revert v; decide
      rcases hv with rfl | rfl
      · exact hy0
      · simp [omegaStrictSol, hy1, omegaLat, OmegaTwo.le]
  have hmop : IsMOPAt omegaLat omegaStrictCFG 1 .omega := by
    refine ⟨?_, ?_⟩
    · rintro b ⟨p, rfl⟩
      obtain ⟨k, hk⟩ := omegaStrictCFG_walk_val_fin p
      rw [hk]; simp [omegaLat, OmegaTwo.le]
    · intro u hu
      cases u with
      | fin m =>
        have := hu _ (omegaStrictCFG_pathVals_one m)
        simp [omegaLat, OmegaTwo.le] at this
        omega
      | omega => simp [omegaLat, OmegaTwo.le]
      | omega1 => simp [omegaLat, OmegaTwo.le]
  refine ⟨omegaLat_isJSL, omegaLat_not_acc, hdist, hstrict, hall, hleast, hmop, fun h => ?_⟩
  have := IsMOPAt.unique omegaLat_isJSL h hmop
  simp [omegaStrictSol] at this

def strictBBDiamond : CFG 5 (Fin 2 → Bool) :=
  diamond (fun _ => true)
    (genKill (fun _ => false) (fun i => decide (i = 1)))
    (genKill (fun _ => false) (fun i => decide (i = 0)))
    bothBits

def strictBBSol : Fin 5 → Fin 2 → Bool :=
  diamondSol (bvLat 2) (fun _ => true)
    (genKill (fun _ => false) (fun i => decide (i = 1)))
    (genKill (fun _ => false) (fun i => decide (i = 0)))
    bothBits

/-- Counterexample (exactness without distributivity, all transfers strict): a
bit-vector diamond whose branches kill one bit each from the full set and whose
join node computes the monotone, non-distributive `bothBits`. -/
theorem strict_exactness_needs_distributive :
    (bvLat 2).IsJSL ∧ (bvLat 2).AscendingChainCondition ∧
      AllReachable strictBBDiamond ∧ (∀ u, Strict (bvLat 2) (strictBBDiamond.f u)) ∧
      (∀ u, Monotone (bvLat 2) (strictBBDiamond.f u)) ∧
      ¬ (∀ u, Distributive (bvLat 2) (strictBBDiamond.f u)) ∧
      IsLeastSolution (bvLat 2) strictBBDiamond strictBBSol ∧
      ¬ IsMOPAt (bvLat 2) strictBBDiamond 4 (strictBBSol 4) := by
  have hgk : ∀ gen kill : Fin 2 → Bool, Monotone (bvLat 2) (genKill gen kill) :=
    fun gen kill => monotone_of_distributive (bvLat_isJSL 2) (genKill_distributive gen kill)
  have hls : IsLeastSolution (bvLat 2) strictBBDiamond strictBBSol :=
    diamondSol_isLeastSolution_of_monotone (bvLat_isJSL 2) _ (hgk _ _) (hgk _ _) bothBits_monotone
  refine ⟨bvLat_isJSL 2, bvLat_acc 2, diamond_allReachable _ _ _ _, ?_, ?_,
    fun h => bothBits_not_distributive (h 3), hls, fun h => ?_⟩
  · intro u
    rcases fin5_cases u with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact (genKill_strict_iff _ _).2 rfl
    · exact (genKill_strict_iff _ _).2 rfl
    · rfl
    · rfl
  · intro u
    rcases fin5_cases u with rfl | rfl | rfl | rfl | rfl
    · exact fun _ _ h => h
    · exact hgk _ _
    · exact hgk _ _
    · exact bothBits_monotone
    · exact fun _ _ h => h
  · have := (diamond_isMOPAt_iff (bvLat_isJSL 2) (fun _ => true)
        (genKill (fun _ => false) (fun i => decide (i = 1)))
        (genKill (fun _ => false) (fun i => decide (i = 0))) bothBits hls).1 (by
      intro v
      by_cases hv : v = 4
      · subst hv; exact h
      · have hv' := diamond_isMOPAt (bvLat_isJSL 2) (fun _ => true)
          (genKill (fun _ => false) (fun i => decide (i = 1)))
          (genKill (fun _ => false) (fun i => decide (i = 0))) bothBits v
        rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl
        all_goals first | exact absurd rfl hv | simpa [strictBBSol, diamondSol, diamondMOP] using hv')
    have := congrFun this 0
    simp [bothBits, genKill, bvLat] at this

/-- Counterexample (exactness for a non-least solution, all transfers strict and of
gen/kill form): a one-node self-loop with identity gen/kill transfer; the full set
is a solution, not least, and not the MOP value. -/
theorem strict_and_genKill_exactness_needs_least :
    let G : CFG 1 (Fin 1 → Bool) := ⟨[(0, 0)], 0, fun _ => false, fun _ => genKill (fun _ => false) (fun _ => false)⟩
    let x : Fin 1 → Fin 1 → Bool := fun _ _ => true
    (bvLat 1).IsJSL ∧ (bvLat 1).AscendingChainCondition ∧
      (∀ u, Distributive (bvLat 1) (G.f u)) ∧
      (∀ u, Strict (bvLat 1) (G.f u)) ∧
      AllReachable G ∧
      (∀ u, G.f u = genKill (fun _ => false) (fun _ => false)) ∧
      (∀ u, ¬ Reachable G u → (fun _ : Fin 1 => false) = fun _ => false) ∧
      IsSolution (bvLat 1) G x ∧ ¬ IsLeastSolution (bvLat 1) G x ∧
      ¬ IsMOPAt (bvLat 1) G 0 (x 0) := by
  intro G x
  have hall : AllReachable G := fun v => by
    have : v = 0 := by revert v; decide
    subst this; exact ⟨.nil⟩
  refine ⟨bvLat_isJSL 1, bvLat_acc 1, fun _ => genKill_distributive _ _,
    fun _ => (genKill_strict_iff _ _).2 rfl, hall, fun _ => rfl, fun _ _ => rfl,
    ⟨by decide, by decide⟩, fun h => ?_, fun h => ?_⟩
  · have hbot : IsSolution (bvLat 1) G (fun _ _ => false) := ⟨by decide, by decide⟩
    have := h.2 _ hbot 0 0 rfl
    simp at this
  · have hub : (bvLat 1).IsUB (pathVals G 0) (fun _ => false) := by
      intro b ⟨p, hp⟩
      have hpval : ∀ {v : Fin 1} (q : Walk G v), q.val = fun _ => false := by
        intro v q
        induction q with
        | nil => rfl
        | snoc q _ ih =>
          show genKill (fun _ => false) (fun _ => false) q.val = _
          rw [ih]; funext i; simp [genKill]
      rw [← hp, hpval p]
      exact (bvLat_isJSL 1).refl _
    have := h.2 _ hub 0 rfl
    simp at this

/-- The exactness theorem applies on a lattice with the ascending chain condition but
no finite height bound. -/
theorem exactness_holds_on_unboundedChainsLat :
    ∃ (G : CFG 2 UnboundedChains) (x : Fin 2 → UnboundedChains),
      (∀ u, Distributive unboundedChainsLat (G.f u)) ∧
      UnreachableStrict unboundedChainsLat G ∧
      IsLeastSolution unboundedChainsLat G x ∧
      ∀ v, IsMOPAt unboundedChainsLat G v (x v) := by
  let G : CFG 2 UnboundedChains := ⟨[(0, 1)], 0, .bot, fun _ => id⟩
  let x : Fin 2 → UnboundedChains := fun _ => .bot
  have hdist : ∀ u, Distributive unboundedChainsLat (G.f u) := fun _ _ _ => rfl
  have hstrict : UnreachableStrict unboundedChainsLat G := fun _ _ => rfl
  have hx : IsLeastSolution unboundedChainsLat G x := by
    refine ⟨⟨by simp [G, x, unboundedChainsLat, UnboundedChains.le], by
      intro u w _
      exact unboundedChainsLat_isJSL.bot_le _⟩, fun y _ v => unboundedChainsLat_isJSL.bot_le _⟩
  exact ⟨G, x, hdist, hstrict, hx, fun v =>
    isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict unboundedChainsLat G
      unboundedChainsLat_isJSL unboundedChainsLat_acc hdist hstrict hx v⟩

/-- Canonical counterexamples for the existence form
`exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict` and its
gen/kill form: dropping the ascending chain condition (`omegaCFG`), distributivity
(`cpDiamond`), strictness at unreachable nodes (`ugCFG`), or the gen/kill form
(`bbDiamond`), with the other hypotheses as in `exactness_needs_acc`,
`exactness_needs_distributive`, `exactness_needs_unreachableStrict` and
`genKill_exactness_needs_genKill_form`, no least solution equals MOP everywhere. -/
theorem exists_exactness_counterexamples :
    (¬ ∃ x, IsLeastSolution omegaLat omegaCFG x ∧ ∀ v, IsMOPAt omegaLat omegaCFG v (x v)) ∧
      (¬ ∃ x, IsLeastSolution cpLat (cpDiamond ⟨.top, .top, .top⟩) x ∧
        ∀ v, IsMOPAt cpLat (cpDiamond ⟨.top, .top, .top⟩) v (x v)) ∧
      (¬ ∃ x, IsLeastSolution (bvLat 1) ugCFG x ∧ ∀ v, IsMOPAt (bvLat 1) ugCFG v (x v)) ∧
      (¬ ∃ x, IsLeastSolution (bvLat 2) bbDiamond x ∧ ∀ v, IsMOPAt (bvLat 2) bbDiamond v (x v)) := by
  refine ⟨fun ⟨x, hx, hm⟩ => ?_, fun ⟨x, hx, hm⟩ => ?_, fun ⟨x, hx, hm⟩ => ?_,
    fun ⟨x, hx, hm⟩ => ?_⟩
  · have e := IsLeastSolution.unique omegaLat_isJSL hx exactness_needs_acc.2.2.2.2.2.1
    exact exactness_needs_acc.2.2.2.2.2.2.2 (e ▸ hm 1)
  · exact (cpDiamond_mfp_x_top_ne_mop_x_const3 _ hx).2.2 (hm 4)
  · have e := IsLeastSolution.unique (bvLat_isJSL 1) hx exactness_needs_unreachableStrict.2.2.2.2.2.2.1
    exact exactness_needs_unreachableStrict.2.2.2.2.2.2.2.2 (e ▸ hm 2)
  · have e := IsLeastSolution.unique (bvLat_isJSL 2) hx genKill_exactness_needs_genKill_form.2.2.2.2.1
    exact genKill_exactness_needs_genKill_form.2.2.2.2.2 (e ▸ hm 4)

/-- Canonical counterexamples for the existence theorem
`exists_isLeastSolution_of_monotone_of_acc`: without the ascending chain condition
the successor loop on `ℕ` has no solution at all, and without monotonicity the
`{id, not}` diamond on `boolLat` (which has the ascending chain condition) has no
least solution. -/
theorem exists_isLeastSolution_counterexamples :
    (natMaxLat.IsJSL ∧ ¬ natMaxLat.AscendingChainCondition ∧
        (∀ u, Monotone natMaxLat (succCFG.f u)) ∧ ¬ ∃ x, IsLeastSolution natMaxLat succCFG x) ∧
      (boolLat.IsJSL ∧ boolLat.AscendingChainCondition ∧
        ¬ (∀ u, Monotone boolLat ((diamond false id (fun b => !b) (fun b => !b)).f u)) ∧
        ¬ ∃ x, IsLeastSolution boolLat (diamond false id (fun b => !b) (fun b => !b)) x) := by
  refine ⟨⟨natMaxLat_isJSL, natMaxLat_not_acc, kildall_needs_heightLe.2.1, ?_⟩,
    ⟨boolLat_isJSL, boolLat_acc, fun h => not_not_monotone (h 2), fun ⟨x, hx⟩ => idNot_viol1 x hx⟩⟩
  rintro ⟨x, hx, _⟩
  have := hx.2 0 0 (by decide)
  simp [succCFG, natMaxLat] at this
  omega

/-- For the corollaries: the instance of `exactness_needs_unreachableStrict` has an
unreachable node and a non-strict transfer, so it also refutes the corollaries
without `AllReachable` and without `∀ u, Strict` (all their other hypotheses hold
there, see `exactness_needs_unreachableStrict`). -/
theorem exactness_corollaries_need_allReachable_or_strict :
    ¬ AllReachable ugCFG ∧ ¬ (∀ u, Strict (bvLat 1) (ugCFG.f u)) ∧
      IsLeastSolution (bvLat 1) ugCFG ugSol ∧ ¬ IsMOPAt (bvLat 1) ugCFG 2 (ugSol 2) := by
  obtain ⟨_, _, _, _, hnr, hns, hls, _, hnot⟩ := exactness_needs_unreachableStrict
  exact ⟨fun h => hnr (h 1), fun h => hns (unreachableStrict_of_strict _ h), hls, hnot⟩

end Toy.Dataflow
