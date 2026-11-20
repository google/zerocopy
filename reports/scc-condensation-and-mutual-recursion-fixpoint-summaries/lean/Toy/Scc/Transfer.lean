/-
Toy.Scc.Transfer
================

Bottom-up fixpoint transfer (cards `bottomup-lfp`, `bottomup-gfp`, `bottomup-mixed`)
and the counterexamples about mixing signs, merging, splitting and ordering
(cards `mixed-neither`, `merge-convex`, `merge-nonconvex`, `split-scc`, `caller-first`).
-/
import Toy.Scc.Fixpoint

namespace Toy.Scc

/-! ## From hierarchical solutions to global extremal fixpoints (fully proved helpers) -/

/-- The global least fixpoint solves every block with its least block fixpoint (meet with
any block fixpoint is a prefixpoint). -/
theorem hierSolution_of_isLeastFixpoint {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    (comp : Fin n → Fin k) {μ : Summ n m} (hμ : IsLeastFixpoint F μ) :
    HierSolution F comp (fun _ => true) μ := by
  intro c
  refine ⟨?_, fun τ hτ => ?_⟩
  · funext f; by_cases hf : comp f = c <;> simp [blockOp, hf, hμ.1]
  · show Le μ τ
    let ρ : Summ n m := fun f i => μ f i && τ f i
    have hρμ : Le ρ μ := fun f i h => by simp only [ρ, Bool.and_eq_true] at h; exact h.1
    have hρτ : Le ρ τ := fun f i h => by simp only [ρ, Bool.and_eq_true] at h; exact h.2
    have hρ : Le (F ρ) ρ := by
      intro f i hF
      have hμfi : μ f i = true := by
        have := hmono ρ μ hρμ f i hF; rwa [hμ.1] at this
      have hτfi : τ f i = true := by
        have e1 := congrFun hτ f
        by_cases hf : comp f = c
        · simp only [blockOp, hf, ↓reduceIte] at e1
          have := hmono ρ τ hρτ f i hF; rwa [e1] at this
        · simp only [blockOp, hf, ↓reduceIte] at e1
          rw [← e1]; exact hμfi
      simp [ρ, hμfi, hτfi]
    have := le_of_monotone_of_isLeastFixpoint_of_prefixpoint hmono hμ hρ
    exact this.trans hρτ

/-- The global greatest fixpoint solves every block with its greatest block fixpoint (join
with any block fixpoint is a postfixpoint). -/
theorem hierSolution_of_isGreatestFixpoint {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    (comp : Fin n → Fin k) {ν : Summ n m} (hν : IsGreatestFixpoint F ν) :
    HierSolution F comp (fun _ => false) ν := by
  intro c
  refine ⟨?_, fun τ hτ => ?_⟩
  · funext f; by_cases hf : comp f = c <;> simp [blockOp, hf, hν.1]
  · show Le τ ν
    let ρ : Summ n m := fun f i => ν f i || τ f i
    have hνρ : Le ν ρ := fun f i h => by simp [ρ, h]
    have hτρ : Le τ ρ := fun f i h => by simp [ρ, h]
    have hρ : Le ρ (F ρ) := by
      intro f i hρfi
      simp only [ρ, Bool.or_eq_true] at hρfi
      rcases hρfi with hν' | hτ'
      · have := hmono ν ρ hνρ f i (by rw [hν.1]; exact hν'); exact this
      · have e1 := congrFun hτ f
        by_cases hf : comp f = c
        · simp only [blockOp, hf, ↓reduceIte] at e1
          exact hmono τ ρ hτρ f i (by rw [e1]; exact hτ')
        · simp only [blockOp, hf, ↓reduceIte] at e1
          rw [← e1] at hτ'
          exact hmono ν ρ hνρ f i (by rw [hν.1]; exact hτ')
    exact hτρ.trans (le_of_monotone_of_isGreatestFixpoint_of_postfixpoint hmono hν hρ)

/-! ## Card `bottomup-lfp` -/

/-- Bottom-up least fixpoint transfer: for monotone `F` that reads only callees, any
block map processed in one pass over a covering callees-first order (one block solve per
list entry), with inner fuel at least the lattice height `n * m`, yields the global least
fixpoint. -/
theorem bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le {n m k : Nat} {E : Graph n}
    {F : Transfer n m} {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat}
    (hmono : Monotone F) (hresp : RespectsCalls E F) (hcover : Covers comp order)
    (hfirst : CalleesFirst E comp order) (hfuel : n * m ≤ fuel) :
    IsLeastFixpoint F (bottomUpLfp F comp order fuel) := by
  have hμ := iter_bot_isLeastFixpoint_of_monotone_of_height_le hmono (Nat.le_refl (n * m))
  have e := hierSolution_unique hresp hfirst (hierSolution_of_isLeastFixpoint hmono comp hμ)
    (hierSolution_bottomUp hmono hresp hcover hfirst hfuel (fun _ => true) bot)
  unfold bottomUpLfp; rw [← e]; exact hμ

theorem bottomUpLfp_tight_monotone :
    ¬ Monotone negT ∧ RespectsCalls gLoop negT ∧ Covers (oneComp (n := 1)) [0] ∧
      CalleesFirst gLoop oneComp [0] ∧ 1 * 1 ≤ 1 ∧
      ¬ IsLeastFixpoint negT (bottomUpLfp negT oneComp [0] 1) :=
  ⟨not_monotone_negT, negT_respectsCalls, by decide, by decide, by decide,
    fun h => negT_no_fixpoint _ h.1⟩

theorem bottomUpLfp_tight_respectsCalls :
    Monotone chainLfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧ CalleesFirst gEmpty idComp [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ RespectsCalls gEmpty chainLfpT ∧
      ¬ IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [0, 1] 2) :=
  ⟨chainLfpT_monotone, by decide, by decide, by decide, not_respectsCalls_gEmpty_chainLfpT,
    fun h => absurd h.1 (by decide)⟩

/-- Tightness of `hcover`: one self-recursive function whose block is never solved
(there are no cross-block calls, so the empty order is callees-first). -/
theorem bottomUpLfp_tight_covers :
    Monotone (topT (n := 1) (m := 1)) ∧ RespectsCalls gLoop (topT (m := 1)) ∧
      CalleesFirst gLoop oneComp [] ∧ 1 * 1 ≤ 1 ∧ ¬ Covers (oneComp (n := 1)) [] ∧
      ¬ IsLeastFixpoint (topT (n := 1) (m := 1)) (bottomUpLfp (topT (n := 1) (m := 1)) oneComp [] 1) :=
  ⟨topT_monotone, topT_respectsCalls gLoop, by decide, by decide, by decide,
    fun h => absurd h.1 (by decide)⟩

theorem bottomUpLfp_tight_calleesFirst :
    Monotone chainLfpT ∧ RespectsCalls gPath chainLfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ CalleesFirst gPath idComp [0, 1] ∧
      ¬ IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [0, 1] 2) :=
  ⟨chainLfpT_monotone, chainLfpT_respectsCalls, by decide, by decide, by decide,
    fun h => absurd h.1 (by decide)⟩

/-- `chainLfpT` also reads only callees in the 2-cycle. -/
theorem chainLfpT_respectsCalls_gCycle : RespectsCalls gCycle chainLfpT :=
  disjT_respectsCalls (by decide)
theorem chainGfpT_respectsCalls_gCycle : RespectsCalls gCycle chainGfpT :=
  conjT_respectsCalls (by decide)

/-- Tightness of the fuel bound, at a valid SCC decomposition (one block, the 2-cycle). -/
theorem bottomUpLfp_tight_fuel :
    IsSccDecomp gCycle oneComp ∧ Monotone chainLfpT ∧ RespectsCalls gCycle chainLfpT ∧
      Covers (oneComp (n := 2)) [0] ∧ CalleesFirst gCycle oneComp [0] ∧ ¬ (2 * 1 ≤ 1) ∧
      ¬ IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT oneComp [0] 1) :=
  ⟨isSccDecomp_gCycle_one, chainLfpT_monotone, chainLfpT_respectsCalls_gCycle, by decide,
    by decide, by decide, fun h => absurd h.1 (by decide)⟩

/-- On `gMix` (`0 → 0`, `0 → 1`, `1 → 1`): `F 0 = σ 0 ∪ σ 1`, `F 1 = {0} ∪ σ 1`
(both blocks recursive; least fixpoint: everything). -/
def mixLfpT : Transfer 2 1 :=
  disjT (fun f _ => decide (f.val = 1)) (fun f _ g _ => decide (f.val ≤ g.val))

/-- On `gMix`: `F 0 = σ 0 ∩ σ 1`, `F 1 = ∅` (greatest fixpoint: nothing). -/
def mixGfpT : Transfer 2 1 :=
  conjT (fun f _ => decide (f.val = 0)) (fun f _ g _ => decide (f.val ≤ g.val))

theorem mixLfpT_monotone : Monotone mixLfpT := disjT_monotone _ _
theorem mixGfpT_monotone : Monotone mixGfpT := conjT_monotone _ _
theorem mixLfpT_respectsCalls : RespectsCalls gMix mixLfpT := disjT_respectsCalls (by decide)
theorem mixGfpT_respectsCalls : RespectsCalls gMix mixGfpT := conjT_respectsCalls (by decide)

/-- Non-vacuity on a graph with a condensation edge and recursive blocks, where the
transfer reads the recursive summaries. -/
theorem bottomUpLfp_nonvacuous :
    IsSccDecomp gMix idComp ∧ Monotone mixLfpT ∧ RespectsCalls gMix mixLfpT ∧
      Covers (idComp (n := 2)) [1, 0] ∧ CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧
      CondEdge gMix idComp 0 1 ∧ gMix 0 0 = true ∧ gMix 1 1 = true :=
  ⟨isSccDecomp_gMix_id, mixLfpT_monotone, mixLfpT_respectsCalls, by decide, by decide,
    by decide, ⟨by decide, 0, 1, rfl, rfl, by decide⟩, by decide, by decide⟩

/-! ## Card `bottomup-gfp` -/

/-- Bottom-up greatest fixpoint transfer, under the same hypotheses as the least case. -/
theorem bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le {n m k : Nat} {E : Graph n}
    {F : Transfer n m} {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat}
    (hmono : Monotone F) (hresp : RespectsCalls E F) (hcover : Covers comp order)
    (hfirst : CalleesFirst E comp order) (hfuel : n * m ≤ fuel) :
    IsGreatestFixpoint F (bottomUpGfp F comp order fuel) := by
  have hν := iter_top_isGreatestFixpoint_of_monotone_of_height_le hmono (Nat.le_refl (n * m))
  have e := hierSolution_unique hresp hfirst (hierSolution_of_isGreatestFixpoint hmono comp hν)
    (hierSolution_bottomUp hmono hresp hcover hfirst hfuel (fun _ => false) top)
  unfold bottomUpGfp; rw [← e]; exact hν

/-- On the call-free graph, `chainGfpT` reads a non-callee. -/
theorem not_respectsCalls_gEmpty_chainGfpT : ¬ RespectsCalls gEmpty chainGfpT := by
  intro h
  have := h top bot 0 (fun g e => by simp [gEmpty] at e)
  have := congrFun this 0
  revert this; decide

theorem bottomUpGfp_tight_monotone :
    ¬ Monotone negT ∧ RespectsCalls gLoop negT ∧ Covers (oneComp (n := 1)) [0] ∧
      CalleesFirst gLoop oneComp [0] ∧ 1 * 1 ≤ 1 ∧
      ¬ IsGreatestFixpoint negT (bottomUpGfp negT oneComp [0] 1) :=
  ⟨not_monotone_negT, negT_respectsCalls, by decide, by decide, by decide,
    fun h => negT_no_fixpoint _ h.1⟩

theorem bottomUpGfp_tight_respectsCalls :
    Monotone chainGfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧ CalleesFirst gEmpty idComp [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ RespectsCalls gEmpty chainGfpT ∧
      ¬ IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [0, 1] 2) :=
  ⟨chainGfpT_monotone, by decide, by decide, by decide, not_respectsCalls_gEmpty_chainGfpT,
    fun h => absurd h.1 (by decide)⟩

theorem botT_respectsCalls {n m : Nat} (E : Graph n) : RespectsCalls E (botT (m := m)) :=
  fun _ _ _ _ => rfl

/-- Tightness of `hcover`: one self-recursive function whose block is never solved. -/
theorem bottomUpGfp_tight_covers :
    Monotone (botT (n := 1) (m := 1)) ∧ RespectsCalls gLoop (botT (m := 1)) ∧
      CalleesFirst gLoop oneComp [] ∧ 1 * 1 ≤ 1 ∧ ¬ Covers (oneComp (n := 1)) [] ∧
      ¬ IsGreatestFixpoint (botT (n := 1) (m := 1)) (bottomUpGfp (botT (n := 1) (m := 1)) oneComp [] 1) :=
  ⟨botT_monotone, botT_respectsCalls gLoop, by decide, by decide, by decide,
    fun h => absurd h.1 (by decide)⟩

theorem bottomUpGfp_tight_calleesFirst :
    Monotone chainGfpT ∧ RespectsCalls gPath chainGfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ CalleesFirst gPath idComp [0, 1] ∧
      ¬ IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [0, 1] 2) :=
  ⟨chainGfpT_monotone, chainGfpT_respectsCalls, by decide, by decide, by decide,
    fun h => absurd h.1 (by decide)⟩

theorem bottomUpGfp_tight_fuel :
    IsSccDecomp gCycle oneComp ∧ Monotone chainGfpT ∧ RespectsCalls gCycle chainGfpT ∧
      Covers (oneComp (n := 2)) [0] ∧ CalleesFirst gCycle oneComp [0] ∧ ¬ (2 * 1 ≤ 1) ∧
      ¬ IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT oneComp [0] 1) :=
  ⟨isSccDecomp_gCycle_one, chainGfpT_monotone, chainGfpT_respectsCalls_gCycle, by decide,
    by decide, by decide, fun h => absurd h.1 (by decide)⟩

/-- Non-vacuity on a graph with a condensation edge and recursive blocks. -/
theorem bottomUpGfp_nonvacuous :
    IsSccDecomp gMix idComp ∧ Monotone mixGfpT ∧ RespectsCalls gMix mixGfpT ∧
      Covers (idComp (n := 2)) [1, 0] ∧ CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧
      CondEdge gMix idComp 0 1 ∧ gMix 0 0 = true ∧ gMix 1 1 = true :=
  ⟨isSccDecomp_gMix_id, mixGfpT_monotone, mixGfpT_respectsCalls, by decide, by decide,
    by decide, ⟨by decide, 0, 1, rfl, rfl, by decide⟩, by decide, by decide⟩

/-! ## Card `bottomup-mixed`: what a per-block mixture of signs computes -/

/-- Under the hypotheses of `bottomup-lfp`, for every sign assignment and every start
vector, the bottom-up result is a hierarchical solution, and it is the only one. -/
theorem bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le {n m k : Nat} {E : Graph n}
    {F : Transfer n m} {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat}
    (hmono : Monotone F) (hresp : RespectsCalls E F) (hcover : Covers comp order)
    (hfirst : CalleesFirst E comp order) (hfuel : n * m ≤ fuel) (sign : Fin k → Bool)
    (init : Summ n m) :
    HierSolution F comp sign (bottomUp F comp sign order fuel init) ∧
      ∀ σ, HierSolution F comp sign σ → σ = bottomUp F comp sign order fuel init := by
  have hex := hierSolution_bottomUp hmono hresp hcover hfirst hfuel sign init
  exact ⟨hex, fun σ hσ => hierSolution_unique hresp hfirst hσ hex⟩

/-- The conclusion of `bottomup-mixed` fails whenever the computed vector is not a
fixpoint of `F` (fully proved helper). -/
theorem not_hierConclusion_of_not_fixpoint {n m k : Nat} {F : Transfer n m}
    {comp : Fin n → Fin k} {sign : Fin k → Bool} {σ : Summ n m} (h : F σ ≠ σ) :
    ¬ (HierSolution F comp sign σ ∧ ∀ τ, HierSolution F comp sign τ → τ = σ) :=
  fun hc => h hc.1.fixpoint

theorem bottomUpHier_tight_monotone :
    ¬ Monotone negT ∧ RespectsCalls gLoop negT ∧ Covers (oneComp (n := 1)) [0] ∧
      CalleesFirst gLoop oneComp [0] ∧ 1 * 1 ≤ 1 ∧
      ¬ (HierSolution negT oneComp (fun _ => true) (bottomUp negT oneComp (fun _ => true) [0] 1 bot) ∧
        ∀ σ, HierSolution negT oneComp (fun _ => true) σ →
          σ = bottomUp negT oneComp (fun _ => true) [0] 1 bot) :=
  ⟨not_monotone_negT, negT_respectsCalls, by decide, by decide, by decide,
    not_hierConclusion_of_not_fixpoint (negT_no_fixpoint _)⟩

theorem bottomUpHier_tight_respectsCalls :
    Monotone chainLfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧ CalleesFirst gEmpty idComp [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ RespectsCalls gEmpty chainLfpT ∧
      ¬ (HierSolution chainLfpT idComp (fun _ => true)
            (bottomUp chainLfpT idComp (fun _ => true) [0, 1] 2 bot) ∧
        ∀ σ, HierSolution chainLfpT idComp (fun _ => true) σ →
          σ = bottomUp chainLfpT idComp (fun _ => true) [0, 1] 2 bot) :=
  ⟨chainLfpT_monotone, by decide, by decide, by decide, not_respectsCalls_gEmpty_chainLfpT,
    not_hierConclusion_of_not_fixpoint (by decide)⟩

/-- Tightness of `hcover`: one self-recursive function whose block is never solved. -/
theorem bottomUpHier_tight_covers :
    Monotone (topT (n := 1) (m := 1)) ∧ RespectsCalls gLoop (topT (m := 1)) ∧
      CalleesFirst gLoop oneComp [] ∧ 1 * 1 ≤ 1 ∧ ¬ Covers (oneComp (n := 1)) [] ∧
      ¬ (HierSolution (topT (n := 1) (m := 1)) oneComp (fun _ => true)
            (bottomUp (topT (n := 1) (m := 1)) oneComp (fun _ => true) [] 1 bot) ∧
        ∀ σ, HierSolution (topT (n := 1) (m := 1)) oneComp (fun _ => true) σ →
          σ = bottomUp (topT (n := 1) (m := 1)) oneComp (fun _ => true) [] 1 bot) :=
  ⟨topT_monotone, topT_respectsCalls gLoop, by decide, by decide, by decide,
    not_hierConclusion_of_not_fixpoint (by decide)⟩

/-- Tightness of `hfirst`, at a genuinely mixed sign assignment: on the split 2-cycle with
`F 0 = σ 1`, `F 1 = σ 0`, block `0` greatest and block `1` least, both `bot` and `top` are
hierarchical solutions, so uniqueness fails whatever the bottom-up pass returns. -/
theorem bottomUpHier_tight_calleesFirst :
    Monotone swapT ∧ RespectsCalls gCycle swapT ∧ Covers (idComp (n := 2)) [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ CalleesFirst gCycle idComp [0, 1] ∧
      ¬ (HierSolution swapT idComp mixSign (bottomUp swapT idComp mixSign [0, 1] 2 bot) ∧
        ∀ σ, HierSolution swapT idComp mixSign σ →
          σ = bottomUp swapT idComp mixSign [0, 1] 2 bot) := by
  refine ⟨swapT_monotone, swapT_respectsCalls, by decide, by decide,
    not_calleesFirst_gCycle_id _, fun ⟨_, huniq⟩ => ?_⟩
  obtain ⟨hbot, htop, hne⟩ := hierSolution_swapT_gCycle_mixSign_not_unique
  exact hne ((huniq bot hbot).trans (huniq top htop).symm)

theorem bottomUpHier_tight_fuel :
    IsSccDecomp gCycle oneComp ∧ Monotone chainLfpT ∧ RespectsCalls gCycle chainLfpT ∧
      Covers (oneComp (n := 2)) [0] ∧ CalleesFirst gCycle oneComp [0] ∧ ¬ (2 * 1 ≤ 1) ∧
      ¬ (HierSolution chainLfpT oneComp (fun _ => true)
            (bottomUp chainLfpT oneComp (fun _ => true) [0] 1 bot) ∧
        ∀ σ, HierSolution chainLfpT oneComp (fun _ => true) σ →
          σ = bottomUp chainLfpT oneComp (fun _ => true) [0] 1 bot) :=
  ⟨isSccDecomp_gCycle_one, chainLfpT_monotone, chainLfpT_respectsCalls_gCycle, by decide,
    by decide, by decide, not_hierConclusion_of_not_fixpoint (by decide)⟩

/-! ## Card `mixed-neither`: least fixpoint in a callee SCC, greatest in a caller SCC -/

/-- On `gMix` (`0 → 0`, `0 → 1`, `1 → 1`): `F 0 = σ 0 ∪ σ 1`, `F 1 = σ 1`. -/
def mixT : Transfer 2 1 := disjT (fun _ _ => false) (fun f _ g _ => decide (f.val ≤ g.val))

/-- The vector `σ 0 = {0}`, `σ 1 = ∅`. -/
def mixResult : Summ 2 1 := fun f _ => decide (f.val = 0)

theorem mixT_monotone : Monotone mixT := disjT_monotone _ _
theorem mixT_respectsCalls : RespectsCalls gMix mixT := disjT_respectsCalls (by decide)

/-- All hypotheses of `bottomup-mixed` hold; the mixture computes `mixResult`, which is the
hierarchical solution and a fixpoint of `F`, but neither the least nor the greatest
fixpoint (those are `bot` and `top`). -/
theorem mixed_lfp_callee_gfp_caller_neither_lfp_nor_gfp :
    IsSccDecomp gMix idComp ∧ Monotone mixT ∧ RespectsCalls gMix mixT ∧
      Covers (idComp (n := 2)) [1, 0] ∧ CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧
      bottomUp mixT idComp mixSign [1, 0] 2 bot = mixResult ∧
      HierSolution mixT idComp mixSign mixResult ∧ mixT mixResult = mixResult ∧
      IsLeastFixpoint mixT bot ∧ IsGreatestFixpoint mixT top ∧
      ¬ IsLeastFixpoint mixT mixResult ∧ ¬ IsGreatestFixpoint mixT mixResult :=
  ⟨isSccDecomp_gMix_id, mixT_monotone, mixT_respectsCalls, by decide, by decide, by decide,
    by decide, hierSolution_of_hierCertB (fuel := 2) mixT_monotone (by decide), by decide,
    isLeastFixpoint_of_iter_fixed (k := 0) mixT_monotone (by decide),
    isGreatestFixpoint_of_iter_fixed (k := 0) mixT_monotone (by decide),
    fun h => absurd (h.2 bot (by decide)) (by decide),
    fun h => absurd (h.2 top (by decide)) (by decide)⟩

/-- Non-vacuity of `bottomup-mixed`: all hypotheses hold on `gMix`, used with the genuinely
mixed sign assignment `mixSign` (callee block `1` least, caller block `0` greatest). -/
theorem bottomUpHier_nonvacuous :
    Monotone mixT ∧ RespectsCalls gMix mixT ∧ Covers (idComp (n := 2)) [1, 0] ∧
      CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧ mixSign 1 = true ∧ mixSign 0 = false :=
  ⟨mixT_monotone, mixT_respectsCalls, by decide, by decide, by decide, by decide, by decide⟩

/-- Non-vacuity of `le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint`: a
hierarchical solution strictly between the least and the greatest fixpoint. -/
theorem hierBetween_nonvacuous :
    IsLeastFixpoint mixT bot ∧ IsGreatestFixpoint mixT top ∧
      HierSolution mixT idComp mixSign mixResult ∧ mixResult ≠ bot ∧ mixResult ≠ top :=
  ⟨isLeastFixpoint_of_iter_fixed (k := 0) mixT_monotone (by decide),
    isGreatestFixpoint_of_iter_fixed (k := 0) mixT_monotone (by decide),
    hierSolution_of_hierCertB (fuel := 2) mixT_monotone (by decide), by decide, by decide⟩

/-- Tightness of the `HierSolution` hypothesis of the betweenness lemma: `bot` is not a
hierarchical solution of `chainLfpT`, whose only fixpoint is `top`, and it is not
between the least and the greatest fixpoint. -/
theorem hierBetween_tight_hierSolution :
    IsLeastFixpoint chainLfpT top ∧ IsGreatestFixpoint chainLfpT top ∧
      ¬ HierSolution chainLfpT idComp (fun _ => true) bot ∧
      ¬ (Le (top : Summ 2 1) bot ∧ Le (bot : Summ 2 1) top) :=
  ⟨isLeastFixpoint_chainLfpT_top,
    isGreatestFixpoint_of_iter_fixed (k := 0) chainLfpT_monotone (by decide),
    not_hierSolution_chainLfpT_bot _, fun h => absurd h.1 (by decide)⟩

/-- Tightness of the least-fixpoint hypothesis of the betweenness lemma: `top` is a
fixpoint of `idT` but not the least one, and the hierarchical solution `bot` is not above
it. -/
theorem hierBetween_tight_least :
    ¬ IsLeastFixpoint idT top ∧ IsGreatestFixpoint idT top ∧
      HierSolution idT oneComp (fun _ => true) bot ∧
      ¬ (Le (top : Summ 1 1) bot ∧ Le (bot : Summ 1 1) top) :=
  ⟨not_isLeastFixpoint_idT_top, isGreatestFixpoint_idT_top, hierSolution_idT_bot_least,
    fun h => absurd h.1 (by decide)⟩

/-- Tightness of the greatest-fixpoint hypothesis of the betweenness lemma: `bot` is a
fixpoint of `idT` but not the greatest one, and the hierarchical solution `top` is not
below it. -/
theorem hierBetween_tight_greatest :
    IsLeastFixpoint idT bot ∧ ¬ IsGreatestFixpoint idT bot ∧
      HierSolution idT oneComp (fun _ => false) top ∧
      ¬ (Le (bot : Summ 1 1) top ∧ Le (top : Summ 1 1) bot) :=
  ⟨isLeastFixpoint_idT_bot, not_isGreatestFixpoint_idT_bot, hierSolution_idT_top_greatest,
    fun h => absurd h.2 (by decide)⟩

/-- On `gMix`: `F 0 = σ 0 ∩ σ 1`, `F 1 = σ 1`. -/
def mixRevT : Transfer 2 1 := conjT (fun _ _ => true) (fun f _ g _ => decide (f.val ≤ g.val))

/-- Sign assignment: the callee block `1` uses its greatest fixpoint, the caller block `0`
its least. -/
def revSign : Fin 2 → Bool := fun c => decide (c.val = 0)

/-- The vector `σ 0 = ∅`, `σ 1 = {0}`. -/
def revResult : Summ 2 1 := fun f _ => decide (f.val = 1)

theorem mixRevT_monotone : Monotone mixRevT := conjT_monotone _ _
theorem mixRevT_respectsCalls : RespectsCalls gMix mixRevT := conjT_respectsCalls (by decide)

/-- The reverse mixture (greatest fixpoint in the callee SCC, least in the caller SCC) can
also compute neither extremal fixpoint: all hypotheses of `bottomup-mixed` hold, and the
result `revResult` is the hierarchical solution and a fixpoint, but neither the least
(`bot`) nor the greatest (`top`) fixpoint. -/
theorem mixed_gfp_callee_lfp_caller_neither_lfp_nor_gfp :
    IsSccDecomp gMix idComp ∧ Monotone mixRevT ∧ RespectsCalls gMix mixRevT ∧
      Covers (idComp (n := 2)) [1, 0] ∧ CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧
      bottomUp mixRevT idComp revSign [1, 0] 2 bot = revResult ∧
      HierSolution mixRevT idComp revSign revResult ∧ mixRevT revResult = revResult ∧
      IsLeastFixpoint mixRevT bot ∧ IsGreatestFixpoint mixRevT top ∧
      ¬ IsLeastFixpoint mixRevT revResult ∧ ¬ IsGreatestFixpoint mixRevT revResult :=
  ⟨isSccDecomp_gMix_id, mixRevT_monotone, mixRevT_respectsCalls, by decide, by decide,
    by decide, by decide, hierSolution_of_hierCertB (fuel := 2) mixRevT_monotone (by decide),
    by decide,
    isLeastFixpoint_of_iter_fixed (k := 0) mixRevT_monotone (by decide),
    isGreatestFixpoint_of_iter_fixed (k := 0) mixRevT_monotone (by decide),
    fun h => absurd (h.2 bot (by decide)) (by decide),
    fun h => absurd (h.2 top (by decide)) (by decide)⟩

/-! ## Fixtures on `0 → 1 → 2` -/

/-- On `0 → 1 → 2`: `F 2 = {0}`, `F 1 = σ 2`, `F 0 = σ 1` (least fixpoint: everything). -/
def chain3LfpT : Transfer 3 1 :=
  disjT (fun f _ => decide (f.val = 2)) (fun f _ g _ => decide (g.val = f.val + 1))

/-- On `0 → 1 → 2`: `F 2 = ∅`, `F 1 = σ 2`, `F 0 = σ 1` (greatest fixpoint: nothing). -/
def chain3GfpT : Transfer 3 1 :=
  conjT (fun f _ => decide (f.val ≠ 2)) (fun f _ g _ => decide (g.val = f.val + 1))

theorem chain3LfpT_monotone : Monotone chain3LfpT := disjT_monotone _ _
theorem chain3GfpT_monotone : Monotone chain3GfpT := conjT_monotone _ _
theorem chain3LfpT_respectsCalls : RespectsCalls gPath3 chain3LfpT :=
  disjT_respectsCalls (by decide)
theorem chain3GfpT_respectsCalls : RespectsCalls gPath3 chain3GfpT :=
  conjT_respectsCalls (by decide)

/-! ## Card `merge-convex`: a coarser decomposition with a callees-first order still works -/

/-- Merging `0` and `1` of `0 → 1 → 2` into one block (they are not mutually reachable) is
not an SCC decomposition, yet the merged block map has a covering callees-first order with
a genuine cross-block call, and single-pass bottom-up over it gives the global least and
greatest fixpoints. -/
theorem convex_merge_not_scc_still_lfp_and_gfp :
    ¬ IsSccDecomp gPath3 convexMerge3 ∧ IsSccDecomp gPath3 idComp ∧
      Monotone chain3LfpT ∧ RespectsCalls gPath3 chain3LfpT ∧
      Monotone chain3GfpT ∧ RespectsCalls gPath3 chain3GfpT ∧
      Covers convexMerge3 [1, 0] ∧ CalleesFirst gPath3 convexMerge3 [1, 0] ∧
      CondEdge gPath3 convexMerge3 0 1 ∧ 3 * 1 ≤ 3 ∧
      IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT convexMerge3 [1, 0] 3) ∧
      IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT convexMerge3 [1, 0] 3) := by
  refine ⟨not_isSccDecomp_gPath3_convexMerge, isSccDecomp_gPath3_id, chain3LfpT_monotone,
    chain3LfpT_respectsCalls, chain3GfpT_monotone, chain3GfpT_respectsCalls, by decide,
    by decide, ⟨by decide, 1, 2, by decide, by decide, by decide⟩, by decide, ?_, ?_⟩
  · have e : bottomUpLfp chain3LfpT convexMerge3 [1, 0] 3 = iter chain3LfpT 3 bot := by decide
    rw [e]; exact isLeastFixpoint_of_iter_fixed chain3LfpT_monotone (by decide)
  · have e : bottomUpGfp chain3GfpT convexMerge3 [1, 0] 3 = iter chain3GfpT 3 top := by decide
    rw [e]; exact isGreatestFixpoint_of_iter_fixed chain3GfpT_monotone (by decide)

/-! ## Card `merge-nonconvex`: merging across a path breaks single-pass bottom-up -/

/-- Merging the endpoints `0` and `2` of `0 → 1 → 2` (not mutually reachable) creates a
condensation cycle: no order is callees-first, and single-pass bottom-up is wrong for
both duplicate-free orders of the two blocks, for least and for greatest fixpoints,
while the SCC decomposition processed callees first is right. -/
theorem nonconvex_merge_wrong_in_both_orders :
    ¬ Reach gPath3 2 0 ∧ mergeComp3 0 = mergeComp3 2 ∧ ¬ IsSccDecomp gPath3 mergeComp3 ∧
      (∀ order, ¬ CalleesFirst gPath3 mergeComp3 order) ∧
      Monotone chain3LfpT ∧ RespectsCalls gPath3 chain3LfpT ∧
      Monotone chain3GfpT ∧ RespectsCalls gPath3 chain3GfpT ∧
      ¬ IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT mergeComp3 [0, 1] 3) ∧
      ¬ IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT mergeComp3 [1, 0] 3) ∧
      ¬ IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT mergeComp3 [0, 1] 3) ∧
      ¬ IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT mergeComp3 [1, 0] 3) ∧
      IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT idComp [2, 1, 0] 3) ∧
      IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT idComp [2, 1, 0] 3) := by
  refine ⟨not_reach_gPath3_2_0, by decide, not_isSccDecomp_gPath3_merge,
    not_calleesFirst_gPath3_merge, chain3LfpT_monotone, chain3LfpT_respectsCalls,
    chain3GfpT_monotone, chain3GfpT_respectsCalls,
    fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide),
    fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide), ?_, ?_⟩
  · have e : bottomUpLfp chain3LfpT idComp [2, 1, 0] 3 = iter chain3LfpT 3 bot := by decide
    rw [e]; exact isLeastFixpoint_of_iter_fixed chain3LfpT_monotone (by decide)
  · have e : bottomUpGfp chain3GfpT idComp [2, 1, 0] 3 = iter chain3GfpT 3 top := by decide
    rw [e]; exact isGreatestFixpoint_of_iter_fixed chain3GfpT_monotone (by decide)

/-- Escape hatch for `merge-nonconvex`: the non-duplicate-free order `[0, 1, 0]`, which
re-solves the merged block after the middle block, reaches both extremal fixpoints on
this instance. -/
theorem nonconvex_merge_order_0_1_0_recovers_lfp_and_gfp :
    IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT mergeComp3 [0, 1, 0] 3) ∧
      IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT mergeComp3 [0, 1, 0] 3) := by
  refine ⟨?_, ?_⟩
  · have e : bottomUpLfp chain3LfpT mergeComp3 [0, 1, 0] 3 = iter chain3LfpT 3 bot := by decide
    rw [e]; exact isLeastFixpoint_of_iter_fixed chain3LfpT_monotone (by decide)
  · have e : bottomUpGfp chain3GfpT mergeComp3 [0, 1, 0] 3 = iter chain3GfpT 3 top := by decide
    rw [e]; exact isGreatestFixpoint_of_iter_fixed chain3GfpT_monotone (by decide)

/-! ## Card `split-scc`: splitting an SCC breaks single-pass bottom-up -/

/-- On the 2-cycle with two bits: function `f` seeds bit `f` and copies the other bit
from the other function.  Least fixpoint: everything. -/
def splitLfpT : Transfer 2 2 :=
  disjT (fun f i => decide (f.val = i.val))
    (fun f i g j => decide (f.val ≠ i.val ∧ g.val = i.val ∧ j = i))

/-- Dual: function `f` forbids bit `f` and copies the other bit from the other function.
Greatest fixpoint: nothing. -/
def splitGfpT : Transfer 2 2 :=
  conjT (fun f i => decide (f.val ≠ i.val))
    (fun f i g j => decide (f.val ≠ i.val ∧ g.val = i.val ∧ j = i))

theorem splitLfpT_monotone : Monotone splitLfpT := disjT_monotone _ _
theorem splitGfpT_monotone : Monotone splitGfpT := conjT_monotone _ _
theorem splitLfpT_respectsCalls : RespectsCalls gCycle splitLfpT :=
  disjT_respectsCalls (by decide)
theorem splitGfpT_respectsCalls : RespectsCalls gCycle splitGfpT :=
  conjT_respectsCalls (by decide)

/-- Splitting the 2-cycle into singleton blocks: no order is callees-first, and single-pass
bottom-up (inner fuel `4 = n * m`) gives a wrong least fixpoint and a wrong greatest
fixpoint for both duplicate-free orders `[0, 1]` and `[1, 0]`; the one-block SCC
decomposition gives the right ones. -/
theorem split_scc_wrong_lfp_and_gfp_in_both_orders :
    ¬ IsSccDecomp gCycle idComp ∧ IsSccDecomp gCycle oneComp ∧
      (∀ order, ¬ CalleesFirst gCycle idComp order) ∧
      Monotone splitLfpT ∧ RespectsCalls gCycle splitLfpT ∧
      Monotone splitGfpT ∧ RespectsCalls gCycle splitGfpT ∧
      ¬ IsLeastFixpoint splitLfpT (bottomUpLfp splitLfpT idComp [0, 1] 4) ∧
      ¬ IsLeastFixpoint splitLfpT (bottomUpLfp splitLfpT idComp [1, 0] 4) ∧
      ¬ IsGreatestFixpoint splitGfpT (bottomUpGfp splitGfpT idComp [0, 1] 4) ∧
      ¬ IsGreatestFixpoint splitGfpT (bottomUpGfp splitGfpT idComp [1, 0] 4) ∧
      IsLeastFixpoint splitLfpT (bottomUpLfp splitLfpT oneComp [0] 4) ∧
      IsGreatestFixpoint splitGfpT (bottomUpGfp splitGfpT oneComp [0] 4) := by
  refine ⟨not_isSccDecomp_gCycle_id, isSccDecomp_gCycle_one, not_calleesFirst_gCycle_id,
    splitLfpT_monotone, splitLfpT_respectsCalls, splitGfpT_monotone, splitGfpT_respectsCalls,
    fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide),
    fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide), ?_, ?_⟩
  · have e : bottomUpLfp splitLfpT oneComp [0] 4 = iter splitLfpT 4 bot := by decide
    rw [e]; exact isLeastFixpoint_of_iter_fixed splitLfpT_monotone (by decide)
  · have e : bottomUpGfp splitGfpT oneComp [0] 4 = iter splitGfpT 4 top := by decide
    rw [e]; exact isGreatestFixpoint_of_iter_fixed splitGfpT_monotone (by decide)

/-- The three monotone maps `Bool → Bool`: constant `false` (`a = 0`), constant `true`
(`a = 1`), identity (`a = 2`). -/
def oneBitCase (a : Fin 3) (x : Bool) : Bool :=
  if a.val = 0 then false else if a.val = 1 then true else x

/-- One bit per function on the 2-cycle: `F 0 = oneBitCase a (σ 1)`, `F 1 = oneBitCase b (σ 0)`.
These nine transfers are all the monotone transfers on `Summ 2 1` that read only callees
in the 2-cycle. -/
def splitOneBitT (a b : Fin 3) : Transfer 2 1 :=
  fun σ f _ => if f.val = 0 then oneBitCase a (σ 1 0) else oneBitCase b (σ 0 0)

theorem oneBitCase_mono (a : Fin 3) {x y : Bool} (h : x = true → y = true)
    (hx : oneBitCase a x = true) : oneBitCase a y = true := by
  unfold oneBitCase at *
  split at hx
  · simp at hx
  · split at hx
    · simp_all
    · simp_all

theorem splitOneBitT_monotone (a b : Fin 3) : Monotone (splitOneBitT a b) := by
  intro σ τ h f i hf
  simp only [splitOneBitT] at hf ⊢
  split at hf
  · simp only [*, ↓reduceIte]; exact oneBitCase_mono a (h 1 0) hf
  · simp only [*, ↓reduceIte]; exact oneBitCase_mono b (h 0 0) hf

theorem splitOneBitT_respectsCalls (a b : Fin 3) : RespectsCalls gCycle (splitOneBitT a b) := by
  intro σ τ f h
  funext i
  simp only [splitOneBitT]
  split
  · next hf =>
    have hf0 : f = 0 := Fin.ext hf
    subst hf0; rw [h 1 (by decide)]
  · next hf =>
    have hf1 : f = 1 := Fin.ext (by have := f.isLt; omega)
    subst hf1; rw [h 0 (by decide)]

/-- Why `split-scc` uses two bits: with one bit per function, each of the nine monotone
callee-local transfers on the split 2-cycle is computed correctly (as its Kleene iterate
at the height `2`, which is its least, resp. greatest, fixpoint by `kleene-bound`) by at
least one of the duplicate-free orders `[0, 1]`, `[1, 0]`. -/
theorem split_scc_one_bit_some_duplicate_free_order_correct :
    ∀ a b : Fin 3,
      (bottomUpLfp (splitOneBitT a b) idComp [0, 1] 2 = iter (splitOneBitT a b) 2 bot ∨
        bottomUpLfp (splitOneBitT a b) idComp [1, 0] 2 = iter (splitOneBitT a b) 2 bot) ∧
      (bottomUpGfp (splitOneBitT a b) idComp [0, 1] 2 = iter (splitOneBitT a b) 2 top ∨
        bottomUpGfp (splitOneBitT a b) idComp [1, 0] 2 = iter (splitOneBitT a b) 2 top) := by
  decide

/-- Escape hatch for `split-scc`: the non-duplicate-free order `[0, 1, 0]` reaches both
extremal fixpoints on this instance. -/
theorem split_scc_order_0_1_0_recovers_lfp_and_gfp :
    IsLeastFixpoint splitLfpT (bottomUpLfp splitLfpT idComp [0, 1, 0] 4) ∧
      IsGreatestFixpoint splitGfpT (bottomUpGfp splitGfpT idComp [0, 1, 0] 4) := by
  refine ⟨?_, ?_⟩
  · have e : bottomUpLfp splitLfpT idComp [0, 1, 0] 4 = iter splitLfpT 4 bot := by decide
    rw [e]; exact isLeastFixpoint_of_iter_fixed splitLfpT_monotone (by decide)
  · have e : bottomUpGfp splitGfpT idComp [0, 1, 0] 4 = iter splitGfpT 4 top := by decide
    rw [e]; exact isGreatestFixpoint_of_iter_fixed splitGfpT_monotone (by decide)

/-! ## Card `caller-first`: a valid SCC decomposition processed in the wrong order -/

/-- With the valid SCC decomposition of `0 → 1`, processing the caller first gives a wrong
least and a wrong greatest fixpoint; callees first gives the right ones. -/
theorem valid_scc_caller_first_order_wrong_lfp_and_gfp :
    IsSccDecomp gPath idComp ∧ Monotone chainLfpT ∧ RespectsCalls gPath chainLfpT ∧
      Monotone chainGfpT ∧ RespectsCalls gPath chainGfpT ∧ 2 * 1 ≤ 2 ∧
      Covers (idComp (n := 2)) [0, 1] ∧ ¬ CalleesFirst gPath idComp [0, 1] ∧
      ¬ IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [0, 1] 2) ∧
      ¬ IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [0, 1] 2) ∧
      IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [1, 0] 2) ∧
      IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [1, 0] 2) := by
  refine ⟨isSccDecomp_gPath_id, chainLfpT_monotone, chainLfpT_respectsCalls,
    chainGfpT_monotone, chainGfpT_respectsCalls, by decide, by decide, by decide,
    fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide), ?_, ?_⟩
  · have e : bottomUpLfp chainLfpT idComp [1, 0] 2 = top := by decide
    rw [e]; exact isLeastFixpoint_chainLfpT_top
  · have e : bottomUpGfp chainGfpT idComp [1, 0] 2 = bot := by decide
    rw [e]; exact isGreatestFixpoint_chainGfpT_bot

/-- Escape hatch for `caller-first`: the non-duplicate-free order `[0, 1, 0]`, which
re-solves the caller after the callee, reaches both extremal fixpoints on this instance. -/
theorem caller_first_order_0_1_0_recovers_lfp_and_gfp :
    IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [0, 1, 0] 2) ∧
      IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [0, 1, 0] 2) := by
  refine ⟨?_, ?_⟩
  · have e : bottomUpLfp chainLfpT idComp [0, 1, 0] 2 = top := by decide
    rw [e]; exact isLeastFixpoint_chainLfpT_top
  · have e : bottomUpGfp chainGfpT idComp [0, 1, 0] 2 = bot := by decide
    rw [e]; exact isGreatestFixpoint_chainGfpT_bot

end Toy.Scc
