import ToyDataflow.Examples
import ToyDataflow.ExactnessExamples
import ToyDataflow.DiamondExamples
import ToyDataflow.KildallExamples

/-!
# Combined counterexamples, degenerate instances and extra witnesses

Supporting theorems only; no definition used by a main result is introduced here.

* Combined counterexamples: each conjunct takes one hypothesis of a main result,
  shows that it fails on a concrete instance, shows that every other hypothesis of
  that result holds on the same instance, and shows that the conclusion fails.
  They restate, in one theorem each, facts that are otherwise spread over a
  per-hypothesis counterexample and a shared "conclusion fails" theorem.
* Degenerate instances: `CFG 0 α` and `CFG n Empty` are uninhabited, so every
  statement quantified over such graphs holds vacuously.
* Extra witnesses: a strict must-orientation gen/kill transfer with a non-empty
  kill set; exactness on a cyclic graph over a lattice with the ascending chain
  condition but no finite height; the MOP value at the reachable node of `ugCFG`;
  irrelevance of the `DecidableRel` instance for the solver.
* Monotone maps on chains: on a totally ordered join-semilattice (in particular on
  `omegaLat`) every monotone map is distributive.
-/

namespace Toy.Dataflow

/-! ## Degenerate instances (vacuous cases) -/

/-- A CFG with zero nodes does not exist: its entry would be an element of `Fin 0`. -/
theorem cfg_zero_empty {α : Type} (G : CFG 0 α) : False :=
  Fin.elim0 G.entry

/-- A CFG over an empty carrier does not exist: its initial value would be an element
of `Empty`. -/
theorem cfg_empty_carrier_empty {n : Nat} (G : CFG n Empty) : False :=
  Empty.elim G.init

/-! ## The `DecidableRel` argument of the solver -/

/-- The result of `kildall` does not depend on which `DecidableRel L.le` instance is
supplied (any two instances are equal). -/
theorem kildall_decidableRel_irrelevant {n : Nat} {α : Type} {L : Lat α}
    (d1 d2 : DecidableRel L.le) (G : CFG n α) (fuel : Nat) :
    @kildall n α L d1 G fuel = @kildall n α L d2 G fuel := by
  have hdec : d1 = d2 := by
    funext a b
    cases d1 a b <;> cases d2 a b <;> first | rfl | contradiction
  subst hdec
  rfl

/-! ## Combined counterexamples -/

/-- For `diamondExact_of_distributiveOnRealizable`: the hypothesis `hL` holds for
`cpLat`, the hypothesis `hd : DistributiveOnRealizable` fails for the
constant-propagation family `cpFamily` with all initial values, and the conclusion
`DiamondExact` fails. -/
theorem diamondExact_needs_distributiveOnRealizable :
    cpLat.IsJSL ∧ ¬ DistributiveOnRealizable cpLat (fun _ => True) cpFamily ∧
      ¬ DiamondExact cpLat (fun _ => True) cpFamily := by
  refine ⟨cpLat_isJSL, fun hd => ?_, diamondExact_iff_nonvacuous.2.2.2⟩
  exact diamondExact_iff_nonvacuous.2.2.2 (diamondExact_of_distributiveOnRealizable cpLat_isJSL hd)

/-- For `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`:
three instances, each violating exactly one of `hacc`, `hdist`, `hstrict` while the
other hypotheses hold, and in each of which no least solution equals MOP at every
node: (1) the two-node successor loop `omegaCFG` on `omegaLat` (no ascending chain
condition); (2) the constant-propagation diamond `cpDiamond ⟨⊤, ⊤, ⊤⟩` (not
distributive); (3) the three-node gen/kill graph `ugCFG` on 1-bit vectors (an
unreachable node with a non-strict transfer). -/
theorem exists_exactness_combined_counterexamples :
    (omegaLat.IsJSL ∧ ¬ omegaLat.AscendingChainCondition ∧
        (∀ u, Distributive omegaLat (omegaCFG.f u)) ∧
        UnreachableStrict omegaLat omegaCFG ∧
        ¬ ∃ x, IsLeastSolution omegaLat omegaCFG x ∧
          ∀ v, IsMOPAt omegaLat omegaCFG v (x v)) ∧
      (cpLat.IsJSL ∧ cpLat.AscendingChainCondition ∧
        ¬ (∀ u, Distributive cpLat ((cpDiamond ⟨.top, .top, .top⟩).f u)) ∧
        UnreachableStrict cpLat (cpDiamond ⟨.top, .top, .top⟩) ∧
        ¬ ∃ x, IsLeastSolution cpLat (cpDiamond ⟨.top, .top, .top⟩) x ∧
          ∀ v, IsMOPAt cpLat (cpDiamond ⟨.top, .top, .top⟩) v (x v)) ∧
      ((bvLat 1).IsJSL ∧ (bvLat 1).AscendingChainCondition ∧
        (∀ u, Distributive (bvLat 1) (ugCFG.f u)) ∧
        ¬ UnreachableStrict (bvLat 1) ugCFG ∧
        ¬ ∃ x, IsLeastSolution (bvLat 1) ugCFG x ∧
          ∀ v, IsMOPAt (bvLat 1) ugCFG v (x v)) := by
  obtain ⟨h1, h2, h3, _, h5, _, _, _⟩ := exactness_needs_acc
  obtain ⟨_, _, _, _, _, hnd, _, _⟩ := exactness_needs_distributive
  obtain ⟨_, _, hdu, _, _, hnus, _, _, _⟩ := exactness_needs_unreachableStrict
  obtain ⟨ex1, ex2, ex3, _⟩ := exists_exactness_counterexamples
  exact ⟨⟨h1, h2, h3, h5, ex1⟩,
    ⟨cpLat_isJSL, cpLat_acc, hnd,
      unreachableStrict_of_allReachable _ (diamond_allReachable _ _ _ _), ex2⟩,
    ⟨bvLat_isJSL 1, bvLat_acc 1, hdu, hnus, ex3⟩⟩

/-- For `genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty`:
(1) on `bbDiamond` (2-bit vectors) no choice of `gen`/`kill` makes every transfer a
gen/kill transfer, the unreachable-gen condition holds for every choice (all nodes
are reachable), and no least solution equals MOP at every node; (2) on `ugCFG`
(1-bit vectors) every transfer is the gen/kill transfer of `ugGen`/`ugKill`, the
unreachable-gen condition fails, and no least solution equals MOP at every node. -/
theorem genKill_exists_exactness_combined_counterexamples :
    ((∀ gen kill : Fin 5 → Fin 2 → Bool,
        ¬ (∀ u, bbDiamond.f u = genKill (gen u) (kill u)) ∧
        (∀ u, ¬ Reachable bbDiamond u → gen u = fun _ => false)) ∧
      ¬ ∃ x, IsLeastSolution (bvLat 2) bbDiamond x ∧
        ∀ v, IsMOPAt (bvLat 2) bbDiamond v (x v)) ∧
      ((∀ u, ugCFG.f u = genKill (ugGen u) (ugKill u)) ∧
        ¬ (∀ u, ¬ Reachable ugCFG u → ugGen u = fun _ => false) ∧
        ¬ ∃ x, IsLeastSolution (bvLat 1) ugCFG x ∧
          ∀ v, IsMOPAt (bvLat 1) ugCFG v (x v)) := by
  obtain ⟨_, hall, _, hnotgk, _, _⟩ := genKill_exactness_needs_genKill_form
  obtain ⟨_, _, ex3, ex4⟩ := exists_exactness_counterexamples
  obtain ⟨hg_ug, hng_ug, _, _⟩ := genKill_exactness_needs_unreachable_gen_empty
  refine ⟨⟨fun gen kill => ⟨fun hG => ?_, fun u hu => absurd (hall u) hu⟩, ex4⟩,
    ⟨hg_ug, hng_ug, ex3⟩⟩
  exact hnotgk ⟨gen 3, kill 3, congrFun (hG 3)⟩

/-- For the corollaries `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`
and `isMOPAt_of_isLeastSolution_of_distributive_of_strict`: on `ugCFG` over 1-bit
vectors, `hL`, `hacc` and `hdist` hold, `hreach : AllReachable` fails, the
all-strict hypothesis fails, `ugSol` is a least solution, and `ugSol 2` is not the
MOP value at node 2. -/
theorem exactness_corollaries_combined_counterexample :
    (bvLat 1).IsJSL ∧ (bvLat 1).AscendingChainCondition ∧
      (∀ u, Distributive (bvLat 1) (ugCFG.f u)) ∧
      ¬ AllReachable ugCFG ∧ ¬ (∀ u, Strict (bvLat 1) (ugCFG.f u)) ∧
      IsLeastSolution (bvLat 1) ugCFG ugSol ∧
      ¬ IsMOPAt (bvLat 1) ugCFG 2 (ugSol 2) := by
  obtain ⟨hjsl, hacc, hdist, _, _, _, _, _, _⟩ := exactness_needs_unreachableStrict
  obtain ⟨hnall, hnstr, hls, hnot⟩ := exactness_corollaries_need_allReachable_or_strict
  exact ⟨hjsl, hacc, hdist, hnall, hnstr, hls, hnot⟩

/-! ## Extra witnesses -/

/-- A must-orientation gen/kill transfer with a non-empty kill set that is both
distributive and strict on `bvMustLat 2` (`gen = kill = {0}`, so `kill ⊆ gen`). -/
theorem genKill_must_strict_nonempty_kill_nonvacuous :
    let gen : Fin 2 → Bool := fun i => decide (i = 0)
    let kill : Fin 2 → Bool := fun i => decide (i = 0)
    (∃ i, kill i = true) ∧
      Distributive (bvMustLat 2) (genKill gen kill) ∧
      Strict (bvMustLat 2) (genKill gen kill) := by
  intro gen kill
  exact ⟨⟨0, rfl⟩, genKill_distributive_must gen kill,
    (genKill_strict_must_iff gen kill).2 (fun _ h => h)⟩

private theorem cw_ub_join_top_left (x : UnboundedChains) :
    unboundedChainsLat.join .top x = .top := by
  cases x <;> rfl

private theorem cw_ub_join_top_right (x : UnboundedChains) :
    unboundedChainsLat.join x .top = .top := by
  cases x <;> rfl

private theorem cw_ub_join_bot_right (x : UnboundedChains) :
    unboundedChainsLat.join x .bot = x := by
  cases x <;> rfl

private theorem cw_stepMid_eq_top_of_gt {m m' k : Nat} (h : m' ≠ m ∨ m < k) :
    stepMid m (.mid m' k) = .top := by
  rcases h with hne | hlt
  · simp [stepMid, hne]
  · by_cases hm : m' = m
    · subst hm
      have h1 : ¬ k < m' := by omega
      have h2 : k ≠ m' := by omega
      simp [stepMid, h1, h2]
    · simp [stepMid, hm]

private theorem cw_join_eq_left_of_le {α : Type} {L : Lat α} (hL : L.IsJSL) {a b : α}
    (h : L.le b a) : L.join a b = a :=
  hL.antisymm _ _ (Lat.join_le hL (hL.refl a) h) (Lat.le_join_left hL a b)

/-- `stepMid m` distributes over joins in `unboundedChainsLat`. -/
theorem stepMid_distributive (m : Nat) : Distributive unboundedChainsLat (stepMid m) := by
  intro a b
  cases a with
  | bot => rfl
  | top =>
    show stepMid m (unboundedChainsLat.join .top b) =
      unboundedChainsLat.join (stepMid m .top) (stepMid m b)
    rw [cw_ub_join_top_left]
    simp [stepMid, cw_ub_join_top_left]
  | mid m₁ k₁ =>
    cases b with
    | bot =>
      show stepMid m (unboundedChainsLat.join (.mid m₁ k₁) .bot) =
        unboundedChainsLat.join (stepMid m (.mid m₁ k₁)) (stepMid m .bot)
      rw [cw_ub_join_bot_right]
      simp [stepMid, cw_ub_join_bot_right]
    | top =>
      show stepMid m (unboundedChainsLat.join (.mid m₁ k₁) .top) =
        unboundedChainsLat.join (stepMid m (.mid m₁ k₁)) (stepMid m .top)
      rw [cw_ub_join_top_right]
      simp [stepMid, cw_ub_join_top_right]
    | mid m₂ k₂ =>
      by_cases hm12 : m₁ = m₂
      · subst hm12
        by_cases hle : k₁ ≤ m₁ ∧ k₂ ≤ m₁
        · rcases Nat.le_total k₁ k₂ with h12 | h21
          · have hab : unboundedChainsLat.le (.mid m₁ k₁) (.mid m₁ k₂) :=
              Or.inr ⟨rfl, h12, hle.2⟩
            rw [Lat.join_eq_right_of_le unboundedChainsLat_isJSL hab,
              Lat.join_eq_right_of_le unboundedChainsLat_isJSL (stepMid_monotone m _ _ hab)]
          · have hba : unboundedChainsLat.le (.mid m₁ k₂) (.mid m₁ k₁) :=
              Or.inr ⟨rfl, h21, hle.1⟩
            rw [cw_join_eq_left_of_le unboundedChainsLat_isJSL hba,
              cw_join_eq_left_of_le unboundedChainsLat_isJSL (stepMid_monotone m _ _ hba)]
        · by_cases hk : k₁ = k₂
          · subst hk
            rw [Lat.join_self unboundedChainsLat_isJSL, Lat.join_self unboundedChainsLat_isJSL]
          · have hmax : ¬ max k₁ k₂ ≤ m₁ := by omega
            have hj : unboundedChainsLat.join (.mid m₁ k₁) (.mid m₁ k₂) = .top := by
              simp [unboundedChainsLat, UnboundedChains.join, hk, hmax]
            rw [hj]
            have htop : stepMid m .top = .top := rfl
            rw [htop]
            have hbig : m₁ < k₁ ∨ m₁ < k₂ := by omega
            rcases hbig with hk1 | hk2
            · by_cases hm : m₁ = m
              · subst hm; rw [cw_stepMid_eq_top_of_gt (Or.inr hk1), cw_ub_join_top_left]
              · rw [cw_stepMid_eq_top_of_gt (Or.inl hm), cw_ub_join_top_left]
            · by_cases hm : m₁ = m
              · subst hm; rw [cw_stepMid_eq_top_of_gt (Or.inr hk2), cw_ub_join_top_right]
              · rw [cw_stepMid_eq_top_of_gt (Or.inl hm), cw_ub_join_top_left]
      · have hj : unboundedChainsLat.join (.mid m₁ k₁) (.mid m₂ k₂) = .top := by
          simp [unboundedChainsLat, UnboundedChains.join, hm12]
        rw [hj]
        have htop : stepMid m .top = .top := rfl
        rw [htop]
        by_cases hm1 : m₁ = m
        · have hm2 : m₂ ≠ m := fun e => hm12 (hm1.trans e.symm)
          rw [cw_stepMid_eq_top_of_gt (Or.inl hm2), cw_ub_join_top_right]
        · rw [cw_stepMid_eq_top_of_gt (Or.inl hm1), cw_ub_join_top_left]

/-- Exactness on a cyclic graph over a lattice with the ascending chain condition and
no finite height bound: the one-node self-loop `stepMidCFG m` on `unboundedChainsLat`
satisfies every hypothesis of
`exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`, and a
least solution equal to MOP at every node exists. -/
theorem cyclic_exactness_on_unboundedChainsLat (m : Nat) :
    unboundedChainsLat.IsJSL ∧ unboundedChainsLat.AscendingChainCondition ∧
      (∀ h, ¬ unboundedChainsLat.HeightLe h) ∧
      (∀ u, Distributive unboundedChainsLat ((stepMidCFG m).f u)) ∧
      UnreachableStrict unboundedChainsLat (stepMidCFG m) ∧
      ∃ x, IsLeastSolution unboundedChainsLat (stepMidCFG m) x ∧
        ∀ v, IsMOPAt unboundedChainsLat (stepMidCFG m) v (x v) := by
  have hdist : ∀ u, Distributive unboundedChainsLat ((stepMidCFG m).f u) :=
    fun _ => stepMid_distributive m
  have hall : AllReachable (stepMidCFG m) := fun v => by
    have : v = 0 := by revert v; decide
    subst this; exact ⟨.nil⟩
  have hstrict : UnreachableStrict unboundedChainsLat (stepMidCFG m) :=
    unreachableStrict_of_allReachable _ hall
  exact ⟨unboundedChainsLat_isJSL, unboundedChainsLat_acc, unboundedChainsLat_not_heightLe,
    hdist, hstrict,
    exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict
      unboundedChainsLat (stepMidCFG m) unboundedChainsLat_isJSL unboundedChainsLat_acc
      hdist hstrict⟩

/-- In `ugCFG`, the MOP value at the reachable node 2 is the empty bit vector. -/
theorem ugCFG_isMOPAt_two_empty : IsMOPAt (bvLat 1) ugCFG 2 (fun _ => false) := by
  refine ⟨fun b hb => ?_, fun u hu => hu (fun _ => false) ⟨.snoc .nil (by decide), rfl⟩⟩
  rw [ugCFG_pathVals_two b hb]
  exact (bvLat_isJSL 1).refl _

/-! ## Monotone maps on chains -/

/-- On a join-semilattice with bottom whose order is total (a chain), every monotone
map distributes over binary joins. -/
theorem distributive_of_monotone_of_total {α : Type} {L : Lat α} (hL : L.IsJSL)
    (htot : ∀ a b, L.le a b ∨ L.le b a) {f : α → α} (hf : Monotone L f) :
    Distributive L f := by
  intro a b
  rcases htot a b with h | h
  · rw [Lat.join_eq_right_of_le hL h, Lat.join_eq_right_of_le hL (hf _ _ h)]
  · rw [cw_join_eq_left_of_le hL h, cw_join_eq_left_of_le hL (hf _ _ h)]

/-- The order of `omegaLat` (the chain `0 < 1 < 2 < ⋯ < ω < ω+1`) is total. -/
theorem omegaLat_total : ∀ a b : OmegaTwo, omegaLat.le a b ∨ omegaLat.le b a := by
  intro a b
  cases a <;> cases b <;> simp [omegaLat, OmegaTwo.le] <;> omega

/-- Every monotone map on `omegaLat` distributes over binary joins. -/
theorem omegaLat_monotone_distributive (f : OmegaTwo → OmegaTwo) (hf : Monotone omegaLat f) :
    Distributive omegaLat f :=
  distributive_of_monotone_of_total omegaLat_isJSL omegaLat_total hf

end Toy.Dataflow
