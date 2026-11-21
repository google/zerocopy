import ToyDataflow.LatticeExamples
import ToyDataflow.MopMfp
import ToyDataflow.Diamond
import ToyDataflow.GenKill
import ToyDataflow.ConstProp
import ToyDataflow.Kildall

/-!
# Counterexamples (hypothesis tightness), positive controls, and non-vacuity

Each counterexample is stated in canonical form: a concrete instance satisfies all
hypotheses of the named result except one, and the conclusion fails.
-/

namespace Toy.Dataflow

/-! ## A two-node gen/kill loop (non-vacuity witness) -/

/-- Node 0 generates bit 0; node 1 generates bit 1 and kills bit 0. -/
def lgGen : Fin 2 → Fin 2 → Bool := fun u i => decide (i = u)
def lgKill : Fin 2 → Fin 2 → Bool := fun u i => decide (u = 1 ∧ i = 0)

/-- `0 → 1`, `1 → 1` (a loop), gen/kill transfers over `bvLat 2`. -/
def loopGK : CFG 2 (Fin 2 → Bool) where
  edges := [(0, 1), (1, 1)]
  entry := 0
  init := fun _ => false
  f := fun u => genKill (lgGen u) (lgKill u)

/-- Its least solution: `∅` at node 0, `{0, 1}` at node 1. -/
def loopGKSol : Fin 2 → Fin 2 → Bool := fun v _ => decide (v = 1)

theorem loopGK_isLeastSolution : IsLeastSolution (bvLat 2) loopGK loopGKSol := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro y hy v
  have h01 := hy.2 0 1 (by decide)
  have h11 := hy.2 1 1 (by decide)
  have y10 : y 1 0 = true := h01 0 (by simp [loopGK, genKill, lgGen])
  have y11 : y 1 1 = true := h11 1 (by simp [loopGK, genKill, lgGen])
  intro i hi
  have hv : v = 1 := by simpa [loopGKSol] using hi
  subst hv
  have : i = 0 ∨ i = 1 := by revert i; decide
  rcases this with rfl | rfl <;> assumption

theorem loopGK_allReachable : AllReachable loopGK := by
  intro v
  have e01 : ((0 : Fin 2), (1 : Fin 2)) ∈ loopGK.edges := by decide
  have : v = 0 ∨ v = 1 := by revert v; decide
  rcases this with rfl | rfl
  · exact ⟨.nil⟩
  · exact ⟨.snoc .nil e01⟩

/-- Non-vacuity of exactness: all hypotheses hold on the gen/kill loop. -/
theorem exactness_nonvacuous :
    (bvLat 2).IsJSL ∧ (bvLat 2).AscendingChainCondition ∧
      (∀ u, Distributive (bvLat 2) (loopGK.f u)) ∧ UnreachableStrict (bvLat 2) loopGK ∧
      AllReachable loopGK ∧ IsLeastSolution (bvLat 2) loopGK loopGKSol :=
  ⟨bvLat_isJSL 2, bvLat_acc 2, fun _ => genKill_distributive _ _,
    unreachableStrict_of_allReachable _ loopGK_allReachable, loopGK_allReachable,
    loopGK_isLeastSolution⟩

/-- On the loop, MOP at node 1 is `{0, 1}` (from exactness). -/
theorem loopGK_isMOPAt_one : IsMOPAt (bvLat 2) loopGK 1 (loopGKSol 1) :=
  isMOPAt_of_isLeastSolution_of_distributive_of_allReachable (bvLat 2) loopGK (bvLat_isJSL 2)
    (bvLat_acc 2) (fun _ => genKill_distributive _ _) loopGK_allReachable loopGK_isLeastSolution 1

/-- Non-vacuity of soundness: transitivity, monotone transfers, a solution, and a
MOP value, on the gen/kill loop. -/
theorem soundness_nonvacuous :
    (bvLat 2).LeTrans ∧ (∀ u, Monotone (bvLat 2) (loopGK.f u)) ∧
      IsSolution (bvLat 2) loopGK loopGKSol ∧ IsMOPAt (bvLat 2) loopGK 1 (loopGKSol 1) :=
  ⟨(bvLat_isJSL 2).trans, fun _ => monotone_of_distributive (bvLat_isJSL 2) (genKill_distributive _ _),
    loopGK_isLeastSolution.1, loopGK_isMOPAt_one⟩

/-- Non-vacuity of gen/kill exactness. -/
theorem genKill_exactness_nonvacuous :
    (∀ u, loopGK.f u = genKill (lgGen u) (lgKill u)) ∧
      (∀ u, ¬ Reachable loopGK u → lgGen u = fun _ => false) ∧
      IsLeastSolution (bvLat 2) loopGK loopGKSol :=
  ⟨fun _ => rfl, fun u hu => absurd (loopGK_allReachable u) hu, loopGK_isLeastSolution⟩

/-- Counterexample (soundness for a non-solution): on the gen/kill loop, the
all-empty assignment is not a solution and MOP at node 1 (`{0, 1}`) is not below it. -/
theorem soundness_needs_solution :
    (bvLat 2).LeTrans ∧ (∀ u, Monotone (bvLat 2) (loopGK.f u)) ∧
      ¬ IsSolution (bvLat 2) loopGK (fun _ _ => false) ∧
      IsMOPAt (bvLat 2) loopGK 1 (loopGKSol 1) ∧ ¬ (bvLat 2).le (loopGKSol 1) (fun _ => false) ∧
      ∃ p : Walk loopGK 1, ¬ (bvLat 2).le p.val (fun _ => false) := by
  refine ⟨(bvLat_isJSL 2).trans,
    fun _ => monotone_of_distributive (bvLat_isJSL 2) (genKill_distributive _ _), ?_,
    loopGK_isMOPAt_one, by decide, ⟨.snoc .nil (by decide), by decide⟩⟩
  intro h
  have := h.2 0 1 (by decide) 0 (by simp [loopGK, genKill, lgGen])
  simp at this

/-- Counterexample (exactness for a non-least solution): on the gen/kill loop the
all-full assignment is a solution, but at node 0 MOP is `∅`. -/
theorem exactness_needs_least :
    (bvLat 2).IsJSL ∧ (bvLat 2).AscendingChainCondition ∧
      (∀ u, Distributive (bvLat 2) (loopGK.f u)) ∧ UnreachableStrict (bvLat 2) loopGK ∧
      AllReachable loopGK ∧
      IsSolution (bvLat 2) loopGK (fun _ _ => true) ∧
      ¬ IsLeastSolution (bvLat 2) loopGK (fun _ _ => true) ∧
      ¬ IsMOPAt (bvLat 2) loopGK 0 (fun _ => true) := by
  refine ⟨bvLat_isJSL 2, bvLat_acc 2, fun _ => genKill_distributive _ _,
    unreachableStrict_of_allReachable _ loopGK_allReachable, loopGK_allReachable,
    ⟨by decide, by decide⟩, fun h => ?_, fun h => ?_⟩
  · have := h.2 loopGKSol loopGK_isLeastSolution.1 0 0 rfl
    simp [loopGKSol] at this
  have hub : (bvLat 2).IsUB (pathVals loopGK 0) (fun _ => false) := by
    intro b hb
    rw [pathVals_iff] at hb
    rcases hb with ⟨_, rfl⟩ | ⟨u, a, hu, _, _⟩
    · exact (bvLat_isJSL 2).refl _
    · have : ∀ u : Fin 2, (u, (0 : Fin 2)) ∉ loopGK.edges := by decide
      exact absurd hu (this u)
  have := h.2 _ hub 0 rfl
  simp at this

/-- Negative example for `IsLeastSolution`: the all-full assignment solves the
gen/kill loop but is not least. -/
theorem loopGK_full_not_isLeastSolution :
    IsSolution (bvLat 2) loopGK (fun _ _ => true) ∧
      ¬ IsLeastSolution (bvLat 2) loopGK (fun _ _ => true) := by
  refine ⟨⟨by decide, by decide⟩, fun h => ?_⟩
  have := h.2 loopGKSol loopGK_isLeastSolution.1 0 0 rfl
  simp [loopGKSol] at this

/-! ## Soundness needs monotone transfer functions -/

/-- Entry `0` with a self-loop and an edge to `1`; every transfer is negation. -/
def notCFG : CFG 2 Bool where
  edges := [(0, 0), (0, 1)]
  entry := 0
  init := false
  f := fun _ b => !b

def notSol : Fin 2 → Bool := fun v => decide (v = 0)

/-- Counterexample (soundness without monotonicity): `notSol` is the least
solution, MOP at node 1 is `true` (path `0 → 1`), but `true ≰ notSol 1 = false`. -/
theorem soundness_needs_monotone :
    boolLat.LeTrans ∧ ¬ (∀ u, Monotone boolLat (notCFG.f u)) ∧
      IsLeastSolution boolLat notCFG notSol ∧ IsMOPAt boolLat notCFG 1 true ∧
      ¬ boolLat.le true (notSol 1) ∧ ∃ p : Walk notCFG 1, ¬ boolLat.le p.val (notSol 1) := by
  refine ⟨boolLat_isJSL.trans, fun h => not_not_monotone (h 0), ⟨⟨by decide, by decide⟩, ?_⟩,
    ⟨fun _ _ _ => rfl, fun u hu => hu true ⟨.snoc .nil (by decide), rfl⟩⟩, by decide,
    ⟨.snoc .nil (by decide), by decide⟩⟩
  intro y hy v
  have h00 := hy.2 0 0 (by decide)
  have hy0 : y 0 = true := by
    cases h : y 0
    · simp [notCFG, boolLat, h] at h00
    · rfl
  have : v = 0 ∨ v = 1 := by revert v; decide
  rcases this with rfl | rfl
  · intro _; exact hy0
  · intro h; simp [notSol] at h

/-- The least solution of the inequations need not satisfy the equations without
monotonicity: `notSol` is the least solution of `notCFG`, but no assignment solves
the equation at node 0, which reads `x 0 = false ⊔ !(x 0)`. -/
theorem notCFG_isLeastSolution_not_isEquationSolution :
    IsLeastSolution boolLat notCFG notSol ∧ ∀ x, ¬ IsEquationSolution boolLat notCFG x := by
  refine ⟨soundness_needs_monotone.2.2.1, fun x hx => ?_⟩
  have h := hx 0
  cases hb : x 0 <;> simp [eqRHS, notCFG, boolLat, Lat.joinList, hb] at h

/-- Path `0 → 1 → 2` with identity transfers on the non-transitive `notTransLat`. -/
def notTransCFG : CFG 3 (Fin 3) := ⟨[(0, 1), (1, 2)], 0, 0, fun _ => id⟩

/-- Counterexample (soundness without transitivity): on `notTransLat` the identity
assignment solves the inequations of the path `0 → 1 → 2`, the MOP value at node 2
is `0`, and `0 ≰ 2`; at the level of a single path, the path `0 → 1 → 2` has value
`0 ≰ 2`. -/
theorem soundness_needs_leTrans :
    ¬ notTransLat.LeTrans ∧
      (∀ u, Monotone notTransLat (notTransCFG.f u)) ∧
      IsSolution notTransLat notTransCFG (fun v => v) ∧
      IsMOPAt notTransLat notTransCFG 2 0 ∧
      ¬ notTransLat.le 0 2 ∧
      ∃ p : Walk notTransCFG 2, ¬ notTransLat.le p.val 2 := by
  let hwalk : Walk notTransCFG 2 :=
    Walk.snoc (u := 1) (Walk.snoc (u := 0) .nil (by decide)) (by decide)
  refine ⟨notTransLat_not_leTrans, fun _ _ _ h => h, ⟨by decide, by decide⟩,
    ⟨?_, ?_⟩, by decide, ⟨hwalk, by decide⟩⟩
  · intro b ⟨p, hp⟩
    have hpv : ∀ {v : Fin 3} (q : Walk notTransCFG v), q.val = 0 := by
      intro v q
      induction q with
      | nil => rfl
      | snoc q _ ih => exact ih
    rw [← hp, hpv p]
    decide
  · intro u hu
    exact hu 0 ⟨hwalk, rfl⟩

/-- Counterexample (MOP-level soundness when `m` is not the MOP value): on the
gen/kill loop the full set is not the MOP value at node 0, and it is not below the
least solution there. -/
theorem soundness_needs_isMOPAt :
    (bvLat 2).LeTrans ∧ (∀ u, Monotone (bvLat 2) (loopGK.f u)) ∧
      IsSolution (bvLat 2) loopGK loopGKSol ∧
      ¬ IsMOPAt (bvLat 2) loopGK 0 (fun _ => true) ∧
      ¬ (bvLat 2).le (fun _ => true) (loopGKSol 0) :=
  ⟨(bvLat_isJSL 2).trans,
    fun _ => monotone_of_distributive (bvLat_isJSL 2) (genKill_distributive _ _),
    loopGK_isLeastSolution.1, exactness_needs_least.2.2.2.2.2.2.2, by decide⟩

/-! ## Exactness needs the ascending chain condition -/

/-- The chain `0 < 1 < 2 < ⋯ < ω < ω+1`. -/
inductive OmegaTwo where
  | fin (k : Nat)
  | omega
  | omega1
  deriving DecidableEq

namespace OmegaTwo

def le : OmegaTwo → OmegaTwo → Prop
  | fin a, fin b => a ≤ b
  | fin _, _ => True
  | omega, fin _ => False
  | omega, _ => True
  | omega1, omega1 => True
  | omega1, _ => False

def join : OmegaTwo → OmegaTwo → OmegaTwo
  | fin a, fin b => fin (max a b)
  | fin _, b => b
  | omega, fin _ => omega
  | omega, b => b
  | omega1, _ => omega1

/-- Successor on the chain: `k ↦ k + 1`, `ω ↦ ω + 1`, `ω + 1 ↦ ω + 1`. -/
def succ : OmegaTwo → OmegaTwo
  | fin k => fin (k + 1)
  | omega => omega1
  | omega1 => omega1

end OmegaTwo

def omegaLat : Lat OmegaTwo := ⟨OmegaTwo.le, OmegaTwo.join, .fin 0⟩

theorem omegaLat_isJSL : omegaLat.IsJSL where
  refl := by intro a; cases a <;> simp [omegaLat, OmegaTwo.le]
  trans := by
    intro a b c; cases a <;> cases b <;> cases c <;> simp [omegaLat, OmegaTwo.le] <;> omega
  antisymm := by
    intro a b; cases a <;> cases b <;> simp [omegaLat, OmegaTwo.le] <;> omega
  join_le_iff := by
    intro a b c; cases a <;> cases b <;> cases c <;> simp [omegaLat, OmegaTwo.le, OmegaTwo.join, Nat.max_le]
  bot_le := by intro a; cases a <;> simp [omegaLat, OmegaTwo.le]

theorem omegaLat_not_acc : ¬ omegaLat.AscendingChainCondition := by
  intro hwf
  have key : ∀ a : OmegaTwo, Acc (fun a b => omegaLat.lt b a) a → ∀ k, a = .fin k → False := by
    intro a ha
    induction ha with
    | intro a _ ih =>
      intro k hk
      subst hk
      exact ih (.fin (k + 1)) ⟨by simp [omegaLat, OmegaTwo.le], by simp⟩ (k + 1) rfl
  exact key _ (hwf.apply (.fin 0)) 0 rfl

theorem omega_succ_distributive : Distributive omegaLat OmegaTwo.succ := by
  intro a b
  cases a <;> cases b <;> simp [omegaLat, OmegaTwo.join, OmegaTwo.succ] <;> omega

/-- Entry `0 → 1`, loop `1 → 1` with transfer `succ`. -/
def omegaCFG : CFG 2 OmegaTwo where
  edges := [(0, 1), (1, 1)]
  entry := 0
  init := .fin 0
  f := fun u => if u = 1 then OmegaTwo.succ else id

/-- Least solution: `0` at node 0, `ω + 1` at node 1. -/
def omegaSol : Fin 2 → OmegaTwo := fun v => if v = 1 then .omega1 else .fin 0

theorem omegaCFG_walk_val_fin {v : Fin 2} (p : Walk omegaCFG v) : ∃ k, p.val = .fin k := by
  induction p with
  | nil => exact ⟨0, rfl⟩
  | @snoc u w p _ ih =>
    obtain ⟨k, hk⟩ := ih
    by_cases hu : u = 1
    · refine ⟨k + 1, ?_⟩
      show omegaCFG.f u p.val = _
      rw [hk]; simp [omegaCFG, hu, OmegaTwo.succ]
    · refine ⟨k, ?_⟩
      show omegaCFG.f u p.val = _
      rw [hk]; simp [omegaCFG, hu]

theorem omegaCFG_pathVals_one (k : Nat) : pathVals omegaCFG 1 (.fin k) := by
  induction k with
  | zero => exact pathVals_step (u := 0) (by decide) (pathVals_init omegaCFG)
  | succ k ih => exact pathVals_step (u := 1) (by decide) ih

theorem omegaCFG_allReachable : AllReachable omegaCFG := by
  intro v
  have : v = 0 ∨ v = 1 := by revert v; decide
  rcases this with rfl | rfl
  · exact ⟨.nil⟩
  · obtain ⟨p, _⟩ := omegaCFG_pathVals_one 0; exact ⟨p⟩

/-- Counterexample (exactness without the ascending chain condition): on the chain
`ℕ ∪ {ω, ω+1}` every monotone function is distributive, all nodes are reachable,
yet the least solution at node 1 is `ω + 1` while MOP there (the least upper bound
of the path values `0, 1, 2, …`) is `ω`. -/
theorem exactness_needs_acc :
    omegaLat.IsJSL ∧ ¬ omegaLat.AscendingChainCondition ∧
      (∀ u, Distributive omegaLat (omegaCFG.f u)) ∧ AllReachable omegaCFG ∧
      UnreachableStrict omegaLat omegaCFG ∧ IsLeastSolution omegaLat omegaCFG omegaSol ∧
      IsMOPAt omegaLat omegaCFG 1 .omega ∧ ¬ IsMOPAt omegaLat omegaCFG 1 (omegaSol 1) := by
  have hdist : ∀ u, Distributive omegaLat (omegaCFG.f u) := by
    intro u
    by_cases hu : u = 1
    · have e : omegaCFG.f u = OmegaTwo.succ := by simp [omegaCFG, hu]
      rw [e]; exact omega_succ_distributive
    · have e : omegaCFG.f u = id := by simp [omegaCFG, hu]
      rw [e]; exact fun _ _ => rfl
  have hmop : IsMOPAt omegaLat omegaCFG 1 .omega := by
    refine ⟨?_, ?_⟩
    · rintro b ⟨p, rfl⟩
      obtain ⟨k, hk⟩ := omegaCFG_walk_val_fin p
      rw [hk]; simp [omegaLat, OmegaTwo.le]
    · intro u hu
      cases u with
      | fin m =>
        have := hu _ (omegaCFG_pathVals_one (m + 1))
        simp [omegaLat, OmegaTwo.le] at this
        omega
      | omega => simp [omegaLat, OmegaTwo.le]
      | omega1 => simp [omegaLat, OmegaTwo.le]
  have hleast : IsLeastSolution omegaLat omegaCFG omegaSol := by
    refine ⟨⟨by simp [omegaLat, OmegaTwo.le, omegaCFG, omegaSol], ?_⟩, ?_⟩
    · intro u w huw
      simp only [omegaCFG, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at huw
      rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
      · simp [omegaLat, OmegaTwo.le, omegaSol, omegaCFG]
      · simp [omegaLat, OmegaTwo.le, omegaSol, omegaCFG, OmegaTwo.succ]
      · exact h.elim
    · intro y hy v
      have h11 := hy.2 1 1 (by decide)
      have hy1 : y 1 = .omega1 := by
        cases h : y 1 with
        | fin k => simp [omegaCFG, h, omegaLat, OmegaTwo.le, OmegaTwo.succ] at h11 <;> omega
        | omega => simp [omegaCFG, h, omegaLat, OmegaTwo.le, OmegaTwo.succ] at h11
        | omega1 => rfl
      have : v = 0 ∨ v = 1 := by revert v; decide
      rcases this with rfl | rfl
      · exact omegaLat_isJSL.bot_le _
      · simp [omegaSol, hy1, omegaLat, OmegaTwo.le]
  refine ⟨omegaLat_isJSL, omegaLat_not_acc, hdist, omegaCFG_allReachable,
    unreachableStrict_of_allReachable _ omegaCFG_allReachable, hleast, hmop, fun h => ?_⟩
  have := IsMOPAt.unique omegaLat_isJSL h hmop
  simp [omegaSol] at this

/-! ## Exactness needs distributivity (constant propagation) -/

/-- Counterexample (exactness without distributivity): the constant-propagation
diamond satisfies every other hypothesis (lattice laws, finite height, all nodes
reachable, monotone transfers, a least solution) and MFP ≠ MOP at node 4. -/
theorem exactness_needs_distributive :
    cpLat.IsJSL ∧ cpLat.AscendingChainCondition ∧
      AllReachable (cpDiamond ⟨.top, .top, .top⟩) ∧
      UnreachableStrict cpLat (cpDiamond ⟨.top, .top, .top⟩) ∧
      (∀ u, Monotone cpLat ((cpDiamond ⟨.top, .top, .top⟩).f u)) ∧
      ¬ (∀ u, Distributive cpLat ((cpDiamond ⟨.top, .top, .top⟩).f u)) ∧
      IsLeastSolution cpLat (cpDiamond ⟨.top, .top, .top⟩)
        (diamondSol cpLat ⟨.top, .top, .top⟩ (assignYZ 1 2) (assignYZ 2 1) assignXYZ) ∧
      ¬ IsMOPAt cpLat (cpDiamond ⟨.top, .top, .top⟩) 4
        (diamondSol cpLat ⟨.top, .top, .top⟩ (assignYZ 1 2) (assignYZ 2 1) assignXYZ 4) := by
  have hall := diamond_allReachable (⟨.top, .top, .top⟩ : St) (assignYZ 1 2) (assignYZ 2 1) assignXYZ
  refine ⟨cpLat_isJSL, cpLat_acc, hall, unreachableStrict_of_allReachable _ hall, ?_,
    fun h => assignXYZ_not_distributive (h 3), cpDiamond_isLeastSolution _,
    (cpDiamond_mfp_x_top_ne_mop_x_const3 _ (cpDiamond_isLeastSolution _)).2.2⟩
  intro u
  rcases fin5_cases u with rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ h => h
  · exact assignYZ_monotone 1 2
  · exact assignYZ_monotone 2 1
  · exact assignXYZ_monotone
  · exact fun _ _ h => h

/-! ## Exactness needs strictness at unreachable nodes (reachability of `v` alone is not enough) -/

def ugGen : Fin 3 → Fin 1 → Bool := fun u _ => decide (u = 1)
def ugKill : Fin 3 → Fin 1 → Bool := fun _ _ => false

/-- Entry `0 → 2`; node `1` has no incoming edge (unreachable), generates the bit,
and has an edge `1 → 2`. -/
def ugCFG : CFG 3 (Fin 1 → Bool) where
  edges := [(0, 2), (1, 2)]
  entry := 0
  init := fun _ => false
  f := fun u => genKill (ugGen u) (ugKill u)

def ugSol : Fin 3 → Fin 1 → Bool := fun v _ => decide (v = 2)

theorem ugCFG_not_reachable_one : ¬ Reachable ugCFG 1 := by
  rw [reachable_iff_exists_pathVals]
  rintro ⟨b, hb⟩
  rw [pathVals_iff] at hb
  rcases hb with ⟨h, _⟩ | ⟨u, a, hu, _, _⟩
  · exact absurd h (by decide)
  · have : ∀ u : Fin 3, (u, (1 : Fin 3)) ∉ ugCFG.edges := by decide
    exact absurd hu (this u)

theorem ugCFG_pathVals_zero (b : Fin 1 → Bool) : pathVals ugCFG 0 b → b = fun _ => false := by
  intro hb
  rw [pathVals_iff] at hb
  rcases hb with ⟨_, rfl⟩ | ⟨u, a, hu, _, _⟩
  · rfl
  · have : ∀ u : Fin 3, (u, (0 : Fin 3)) ∉ ugCFG.edges := by decide
    exact absurd hu (this u)

theorem ugCFG_pathVals_two (b : Fin 1 → Bool) : pathVals ugCFG 2 b → b = fun _ => false := by
  intro hb
  rw [pathVals_iff] at hb
  rcases hb with ⟨h, _⟩ | ⟨u, a, hu, ha, rfl⟩
  · exact absurd h (by decide)
  · have e : ∀ u : Fin 3, (u, (2 : Fin 3)) ∈ ugCFG.edges → u = 0 ∨ u = 1 := by decide
    have : u = 0 ∨ u = 1 := e u hu
    rcases this with rfl | rfl
    · rw [ugCFG_pathVals_zero a ha]; funext i; simp [ugCFG, genKill, ugGen, ugKill]
    · exact absurd ((reachable_iff_exists_pathVals _ _).2 ⟨a, ha⟩) ugCFG_not_reachable_one

/-- Counterexample (exactness without `UnreachableStrict`): with gen/kill
(distributive) transfers on a finite lattice, node 2 is reachable from the entry,
yet the least solution there is `{0}` while MOP is `∅`, because the unreachable
node 1 generates the bit along its edge into node 2. -/
theorem exactness_needs_unreachableStrict :
    (bvLat 1).IsJSL ∧ (bvLat 1).AscendingChainCondition ∧
      (∀ u, Distributive (bvLat 1) (ugCFG.f u)) ∧
      (∀ u, ugCFG.f u = genKill (ugGen u) (ugKill u)) ∧
      ¬ Reachable ugCFG 1 ∧ ¬ UnreachableStrict (bvLat 1) ugCFG ∧
      IsLeastSolution (bvLat 1) ugCFG ugSol ∧ Reachable ugCFG 2 ∧
      ¬ IsMOPAt (bvLat 1) ugCFG 2 (ugSol 2) := by
  refine ⟨bvLat_isJSL 1, bvLat_acc 1, fun u => genKill_distributive _ _, fun _ => rfl,
    ugCFG_not_reachable_one, fun h => ?_, ⟨⟨by decide, by decide⟩, ?_⟩,
    ⟨.snoc .nil (by decide)⟩, fun h => ?_⟩
  · have := congrFun (h 1 ugCFG_not_reachable_one) 0
    simp [ugCFG, genKill, ugGen, bvLat] at this
  · intro y hy v
    have h12 := hy.2 1 2 (by decide)
    have : y 2 0 = true := h12 0 (by simp [ugCFG, genKill, ugGen])
    intro i hi
    have hv : v = 2 := by simpa [ugSol] using hi
    subst hv
    have : i = 0 := by revert i; decide
    subst this; assumption
  · have hub : (bvLat 1).IsUB (pathVals ugCFG 2) (fun _ => false) := by
      intro b hb
      rw [ugCFG_pathVals_two b hb]
      exact (bvLat_isJSL 1).refl _
    have := h.2 _ hub 0
    simp [ugSol] at this

/-- The same instance refutes gen/kill exactness when an unreachable node has a
non-empty gen set. -/
theorem genKill_exactness_needs_unreachable_gen_empty :
    (∀ u, ugCFG.f u = genKill (ugGen u) (ugKill u)) ∧
      ¬ (∀ u, ¬ Reachable ugCFG u → ugGen u = fun _ => false) ∧
      IsLeastSolution (bvLat 1) ugCFG ugSol ∧ ¬ IsMOPAt (bvLat 1) ugCFG 2 (ugSol 2) := by
  obtain ⟨_, _, _, hG, hnr, _, hls, _, hnot⟩ := exactness_needs_unreachableStrict
  refine ⟨hG, fun h => ?_, hls, hnot⟩
  have := congrFun (h 1 hnr) 0
  simp [ugGen] at this

/-! ## Gen/kill exactness needs gen/kill form -/

/-- Branches set bit 0 and bit 1 respectively (as gen/kill functions that kill
everything); the join node computes `bothBits`, which is not gen/kill. -/
def bbDiamond : CFG 5 (Fin 2 → Bool) :=
  diamond (fun _ => false) (genKill (fun i => decide (i = 0)) (fun _ => true))
    (genKill (fun i => decide (i = 1)) (fun _ => true)) bothBits

def bbSol : Fin 5 → Fin 2 → Bool :=
  diamondSol (bvLat 2) (fun _ => false) (genKill (fun i => decide (i = 0)) (fun _ => true))
    (genKill (fun i => decide (i = 1)) (fun _ => true)) bothBits

/-- Counterexample (gen/kill exactness without gen/kill form at the join node): on
`bvLat 2`, all nodes reachable, monotone transfers, and the least solution at
node 4 is `{0, 1}` while MOP is `∅`. -/
theorem genKill_exactness_needs_genKill_form :
    (bvLat 2).IsJSL ∧ AllReachable bbDiamond ∧ (∀ u, Monotone (bvLat 2) (bbDiamond.f u)) ∧
      ¬ (∃ gen kill, ∀ a, bbDiamond.f 3 a = genKill gen kill a) ∧
      IsLeastSolution (bvLat 2) bbDiamond bbSol ∧ ¬ IsMOPAt (bvLat 2) bbDiamond 4 (bbSol 4) := by
  have hgk : ∀ gen kill : Fin 2 → Bool, Monotone (bvLat 2) (genKill gen kill) :=
    fun gen kill => monotone_of_distributive (bvLat_isJSL 2) (genKill_distributive gen kill)
  have hls : IsLeastSolution (bvLat 2) bbDiamond bbSol :=
    diamondSol_isLeastSolution_of_monotone (bvLat_isJSL 2) _ (hgk _ _) (hgk _ _) bothBits_monotone
  refine ⟨bvLat_isJSL 2, diamond_allReachable _ _ _ _, ?_, ?_, hls, fun h => ?_⟩
  · intro u
    rcases fin5_cases u with rfl | rfl | rfl | rfl | rfl
    · exact fun _ _ h => h
    · exact hgk _ _
    · exact hgk _ _
    · exact bothBits_monotone
    · exact fun _ _ h => h
  · rintro ⟨gen, kill, hgen⟩
    apply bothBits_not_distributive
    intro a b
    have e : bothBits = genKill gen kill := funext hgen
    rw [e]; exact genKill_distributive gen kill a b
  · have := (diamond_isMOPAt_iff (bvLat_isJSL 2) _ _ _ _ hls).1 (by
      intro v
      by_cases hv : v = 4
      · subst hv; exact h
      · have hv' := diamond_isMOPAt (bvLat_isJSL 2) (fun _ => false)
          (genKill (fun i => decide (i = 0)) (fun _ => true))
          (genKill (fun i => decide (i = 1)) (fun _ => true)) bothBits v
        rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl
        all_goals first | exact absurd rfl hv | simpa [bbSol, diamondSol, diamondMOP] using hv')
    have := congrFun this 0
    simp [bothBits, genKill, bvLat] at this

/-! ## The diamond characterization needs monotone families -/

/-- The family `{id, not}` on `boolLat`. -/
def idNotFamily : (Bool → Bool) → Prop := fun φ => φ = id ∨ φ = (fun b => !b)

theorem idNot_viol1 (x : Fin 5 → Bool) :
    ¬ IsLeastSolution boolLat (diamond false id (fun b => !b) (fun b => !b)) x := by
  intro hx
  have e := diamond_isLeastSolution_eq boolLat_isJSL _ _ _ _ hx
  let y : Fin 5 → Bool := fun v => decide (v = 2 ∨ v = 4)
  have hy : IsSolution boolLat (diamond false id (fun b => !b) (fun b => !b)) y :=
    ⟨by decide, by decide⟩
  have := hx.2 y hy 3
  rw [e] at this
  revert this; decide

theorem idNot_viol2 (x : Fin 5 → Bool) :
    ¬ IsLeastSolution boolLat (diamond false (fun b => !b) id (fun b => !b)) x := by
  intro hx
  have e := diamond_isLeastSolution_eq boolLat_isJSL _ _ _ _ hx
  let y : Fin 5 → Bool := fun v => decide (v = 1 ∨ v = 4)
  have hy : IsSolution boolLat (diamond false (fun b => !b) id (fun b => !b)) y :=
    ⟨by decide, by decide⟩
  have := hx.2 y hy 3
  rw [e] at this
  revert this; decide

/-- Counterexample (necessity direction without monotonicity): for `F = {id, not}`
and initial value `false`, every diamond built from `F` that has a least solution
is exact (the two non-distributive combinations have no least solution), yet `not`
does not distribute over the realizable pair `(false, true)`. -/
theorem diamondExact_needs_monotone :
    boolLat.IsJSL ∧ ¬ (∀ φ, idNotFamily φ → Monotone boolLat φ) ∧
      DiamondExact boolLat (· = false) idNotFamily ∧
      ¬ DistributiveOnRealizable boolLat (· = false) idNotFamily := by
  refine ⟨boolLat_isJSL, fun h => not_not_monotone (h _ (Or.inr rfl)), ?_, ?_⟩
  · intro a g h f ha hg hh hf x hx
    subst ha
    apply (diamond_isMOPAt_iff boolLat_isJSL _ _ _ _ hx).2
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;> rcases hf with rfl | rfl
    all_goals first
      | decide
      | exact absurd hx (idNot_viol1 x)
      | exact absurd hx (idNot_viol2 x)
  · intro h
    have := h false id (fun b => !b) (fun b => !b) rfl (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
    revert this; decide

/-! ## The diamond characterization: realizable pairs, not all pairs -/

/-- Positive control for the quantifier: the one-element family `{x := y + z}` is
exact on every diamond built from it (both branches coincide), although its member
is not distributive. So "distributive over all pairs" is sufficient but not
necessary; the exact condition quantifies over realizable pairs only. -/
theorem diamondExact_singleton_of_not_distributive :
    cpLat.IsJSL ∧ cpLat.AscendingChainCondition ∧
      (∀ φ, φ = assignXYZ → Monotone cpLat φ) ∧ (∃ a : St, (fun _ => True) a) ∧
      ¬ (∀ b : St, (fun _ : St => b) = assignXYZ) ∧
      DiamondExact cpLat (fun _ => True) (fun φ => φ = assignXYZ) ∧
      ¬ Distributive cpLat assignXYZ := by
  refine ⟨cpLat_isJSL, cpLat_acc, fun φ h => h ▸ assignXYZ_monotone,
    ⟨⟨.bot, .bot, .bot⟩, trivial⟩, ?_,
    diamondExact_of_distributiveOnRealizable cpLat_isJSL
      (distributiveOnRealizable_singleton cpLat_isJSL _ _),
    assignXYZ_not_distributive⟩
  intro h
  have := congrFun (h ⟨.bot, .bot, .bot⟩) ⟨.top, .const 1, .const 2⟩
  revert this; decide

/-- The constant-propagation family of the diamond program. -/
def cpFamily : (St → St) → Prop :=
  fun φ => φ = assignYZ 1 2 ∨ φ = assignYZ 2 1 ∨ φ = assignXYZ

/-- Non-vacuity of the characterization, with both sides true (gen/kill on
`bvLat 1`) and with both sides false (the constant-propagation family). -/
theorem diamondExact_iff_nonvacuous :
    ((bvLat 1).IsJSL ∧
        (∀ φ, (∃ gen kill, φ = genKill gen kill) → Monotone (bvLat 1) φ) ∧
        DiamondExact (bvLat 1) (fun _ => True) (fun φ => ∃ gen kill, φ = genKill gen kill)) ∧
      (cpLat.IsJSL ∧ (∀ φ, cpFamily φ → Monotone cpLat φ) ∧
        ¬ DiamondExact cpLat (fun _ => True) cpFamily) := by
  refine ⟨⟨bvLat_isJSL 1, ?_, ?_⟩, ⟨cpLat_isJSL, ?_, ?_⟩⟩
  · rintro φ ⟨gen, kill, rfl⟩
    exact monotone_of_distributive (bvLat_isJSL 1) (genKill_distributive gen kill)
  · apply diamondExact_of_distributiveOnRealizable (bvLat_isJSL 1)
    rintro a g h f _ _ _ ⟨gen, kill, rfl⟩
    exact genKill_distributive gen kill _ _
  · rintro φ (rfl | rfl | rfl)
    · exact assignYZ_monotone 1 2
    · exact assignYZ_monotone 2 1
    · exact assignXYZ_monotone
  · intro h
    have := h ⟨.top, .top, .top⟩ (assignYZ 1 2) (assignYZ 2 1) assignXYZ trivial
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) _ (cpDiamond_isLeastSolution _) 4
    exact (cpDiamond_mfp_x_top_ne_mop_x_const3 _ (cpDiamond_isLeastSolution _)).2.2 this

/-- Counterexample (constant-closed corollary without a non-empty set of initial
values): with no initial values every diamond condition holds vacuously, although
the family (all constants plus `x := y + z`) is not distributive. -/
theorem diamondExact_const_needs_nonempty_init :
    cpLat.IsJSL ∧ cpLat.AscendingChainCondition ∧ ¬ (∃ a : St, (fun _ => False) a) ∧
    (∀ φ, ((∃ b, φ = fun _ => b) ∨ φ = assignXYZ) → Monotone cpLat φ) ∧
      (∀ b, (∃ b', (fun _ : St => b) = fun _ => b') ∨ (fun _ : St => b) = assignXYZ) ∧
      DiamondExact cpLat (fun _ => False) (fun φ => (∃ b, φ = fun _ => b) ∨ φ = assignXYZ) ∧
      ¬ (∀ f, ((∃ b, f = fun _ => b) ∨ f = assignXYZ) → Distributive cpLat f) := by
  refine ⟨cpLat_isJSL, cpLat_acc, fun ⟨_, h⟩ => h, ?_, fun b => Or.inl ⟨b, rfl⟩,
    fun _ _ _ _ ha => ha.elim, fun h =>
    assignXYZ_not_distributive (h _ (Or.inr rfl))⟩
  rintro φ (⟨b, rfl⟩ | rfl)
  · exact fun _ _ _ => cpLat_isJSL.refl _
  · exact assignXYZ_monotone

/-! ## Kildall: fuel bound and non-vacuity -/

/-- The one-point lattice. -/
def unitLat : Lat Unit := ⟨fun _ _ => True, fun _ _ => (), ()⟩

instance : DecidableRel unitLat.le := fun _ _ => instDecidableTrue

theorem unitLat_isJSL : unitLat.IsJSL :=
  ⟨fun _ => trivial, fun _ _ _ _ _ => trivial, fun _ _ _ _ => rfl,
    fun _ _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩, fun _ => trivial⟩

theorem unitLat_heightLe_zero : unitLat.HeightLe 0 := by
  intro k c hc
  cases k with
  | zero => exact Nat.le_refl 0
  | succ k => exact absurd rfl (hc 0 (by omega)).2


/-- Counterexample (partial correctness without monotonicity): on `notCFG`, with a
height bound `1` and fuel `10 ≥ 2 * (1 + 1) + 1`, the solver returns `some x` with
`x = (true, true)`; `x` is a solution (as it must be, `kildall_isSolution_of_eq_some`)
but not the least one `(true, false)`. -/
theorem kildall_needs_monotone :
    boolLat.IsJSL ∧ ¬ (∀ u, Monotone boolLat (notCFG.f u)) ∧ boolLat.HeightLe 1 ∧
      2 * (1 + 1) + 1 ≤ 10 ∧
      (∃ x, kildall boolLat notCFG 10 = some x ∧ (x 0, x 1) = (true, true) ∧
        IsSolution boolLat notCFG x ∧ ¬ IsLeastSolution boolLat notCFG x) ∧
      ¬ ∃ x, kildall boolLat notCFG 10 = some x ∧ IsLeastSolution boolLat notCFG x := by
  have hm : (kildall boolLat notCFG 10).map (fun x => (x 0, x 1)) = some (true, true) := by
    decide
  have hnot : ∀ x, kildall boolLat notCFG 10 = some x → ¬ IsLeastSolution boolLat notCFG x := by
    intro x hk hx
    have e := IsLeastSolution.unique boolLat_isJSL hx soundness_needs_monotone.2.2.1
    have hm' := hm
    rw [hk] at hm'
    have h1 : x 1 = true := by simp at hm'; exact hm'.2
    rw [e] at h1
    simp [notSol] at h1
  refine ⟨boolLat_isJSL, fun h => not_not_monotone (h 0), boolLat_heightLe_one, by decide,
    ?_, fun ⟨x, hk, hx⟩ => hnot x hk hx⟩
  cases hk : kildall boolLat notCFG 10 with
  | none => rw [hk] at hm; simp at hm
  | some x =>
    rw [hk] at hm
    exact ⟨x, rfl, by simpa using hm, kildall_isSolution_of_eq_some boolLat_isJSL notCFG hk,
      hnot x hk⟩

/-- `0 → 0` with transfer `n ↦ n + 1` on the natural numbers under `max`. -/
def succCFG : CFG 1 Nat := ⟨[(0, 0)], 0, 0, fun _ n => n + 1⟩

instance : DecidableRel natMaxLat.le := fun a b => Nat.decLe a b

theorem kildallLoop_succCFG (fuel k : Nat) :
    kildallLoop natMaxLat succCFG fuel (fun _ => k) [0] = none := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    have e : (propagate natMaxLat (k + 1) (succs succCFG 0) (fun _ => k) []) =
        (fun _ => k + 1, [0]) := by
      have hs : succs succCFG 0 = [0] := by decide
      rw [hs]
      have hnle : ¬ natMaxLat.le (k + 1) k := by simp [natMaxLat]
      simp only [propagate, hnle, ↓reduceIte]
      congr 1
      funext v
      have : v = 0 := by revert v; decide
      subst this
      simp [upd, natMaxLat]
    show kildallLoop natMaxLat succCFG fuel
      (propagate natMaxLat (k + 1) (succs succCFG 0) (fun _ => k) []).1
      (propagate natMaxLat (k + 1) (succs succCFG 0) (fun _ => k) []).2 = none
    rw [e]
    exact ih (k + 1)

/-- Counterexample (termination without a height bound): on `ℕ` under `max` with a
loop that increments, the solver returns `none` for every amount of fuel. -/
theorem kildall_needs_heightLe :
    natMaxLat.IsJSL ∧ (∀ u, Monotone natMaxLat (succCFG.f u)) ∧
      (∀ u, Distributive natMaxLat (succCFG.f u)) ∧ AllReachable succCFG ∧
      ¬ natMaxLat.AscendingChainCondition ∧ (∀ h, ¬ natMaxLat.HeightLe h) ∧
      ∀ fuel, kildall natMaxLat succCFG fuel = none := by
  refine ⟨natMaxLat_isJSL, fun _ a b hab => Nat.succ_le_succ hab,
    fun _ a b => by simp only [succCFG, natMaxLat]; omega, fun v => ?_, natMaxLat_not_acc,
    natMaxLat_not_heightLe, fun fuel => ?_⟩
  · have : v = 0 := by revert v; decide
    subst this; exact ⟨.nil⟩
  have e : kildallInit natMaxLat succCFG = fun _ => 0 := by
    funext v
    have : v = 0 := by revert v; decide
    subst this; rfl
  have hr : List.finRange 1 = [0] := by decide
  unfold kildall
  rw [e, hr]
  exact kildallLoop_succCFG fuel 0

/-- Counterexample for the hypothesis `h : kildall L G fuel = some x` of partial
correctness: on the gen/kill loop (monotone transfers) the all-full assignment is
not what the solver returns, and it is not the least solution; the all-empty
assignment is not what the solver returns, and it is not a solution. -/
theorem kildall_needs_eq_some :
    (bvLat 2).IsJSL ∧ (∀ u, Monotone (bvLat 2) (loopGK.f u)) ∧
      kildall (bvLat 2) loopGK 7 ≠ some (fun _ _ => true) ∧
      ¬ IsLeastSolution (bvLat 2) loopGK (fun _ _ => true) ∧
      kildall (bvLat 2) loopGK 7 ≠ some (fun _ _ => false) ∧
      ¬ IsSolution (bvLat 2) loopGK (fun _ _ => false) := by
  have hm : (kildall (bvLat 2) loopGK 7).map (fun x => (x 0 0, x 0 1, x 1 0, x 1 1)) =
      some (false, false, true, true) := by decide
  refine ⟨bvLat_isJSL 2, fun _ => monotone_of_distributive (bvLat_isJSL 2)
    (genKill_distributive _ _), fun h => ?_, loopGK_full_not_isLeastSolution.2, fun h => ?_,
    soundness_needs_solution.2.2.1⟩
  · rw [h] at hm
    simp at hm
  · rw [h] at hm
    simp at hm

/-- Non-vacuity of the Kildall theorems on the gen/kill loop: lattice laws,
monotone transfers, height `2`, fuel `7 = 2 * (2 + 1) + 1`; and the computed result
is `∅` at node 0 and `{0, 1}` at node 1. -/
theorem kildall_nonvacuous :
    (bvLat 2).IsJSL ∧ (∀ u, Monotone (bvLat 2) (loopGK.f u)) ∧ (bvLat 2).HeightLe 2 ∧
      2 * (2 + 1) + 1 ≤ 7 ∧
      (kildall (bvLat 2) loopGK 7).map (fun x => (x 0 0, x 0 1, x 1 0, x 1 1)) =
        some (false, false, true, true) :=
  ⟨bvLat_isJSL 2, fun _ => monotone_of_distributive (bvLat_isJSL 2) (genKill_distributive _ _),
    bvLat_heightLe 2, by decide, by decide⟩

end Toy.Dataflow
