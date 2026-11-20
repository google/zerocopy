/-
Toy.Scc.Fixpoint
================

Results about extremal fixpoints on the finite summary lattice and about checking
untrusted summaries (cards `kleene-bound`, `bottomup-one-sided`,
`prefix-postfix-sound`, `checks-not-exact`, `ranked-cert`, `ranked-cert-complete`).
-/
import Toy.Scc.BottomUp

namespace Toy.Scc

/-! ## Fixtures -/

/-- A non-monotone single-function transfer with two bits:
`F σ = ∅` if `σ 0 = {0}`, and `F σ = {0, 1}` otherwise.  Unique fixpoint `top`. -/
def nmLfpT : Transfer 1 2 := fun σ _ _ => !(σ 0 0 && !σ 0 1)

/-- A non-monotone single-function transfer with two bits:
`F σ = {0, 1}` if `σ 0 = {1}`, and `F σ = ∅` otherwise.  Unique fixpoint `bot`. -/
def nmGfpT : Transfer 1 2 := fun σ _ _ => !σ 0 0 && σ 0 1

/-- A non-monotone single-function transfer with two bits:
bit 0 is `¬σ 0 0 ∨ σ 0 1`, bit 1 is `σ 0 1`.  Unique fixpoint `top`, but Kleene
iteration from `bot` oscillates between `∅` and `{0}`. -/
def nmRankT : Transfer 1 2 := fun σ _ i => if i.val = 0 then !σ 0 0 || σ 0 1 else σ 0 1

/-- Constant `bot` (reads nothing). -/
def botT {n m : Nat} : Transfer n m := fun _ => bot

/-- The vector `{0}` for a single function with two bits. -/
def only0 : Summ 1 2 := fun _ i => decide (i.val = 0)
/-- The vector `{1}` for a single function with two bits. -/
def only1 : Summ 1 2 := fun _ i => decide (i.val = 1)

/-- On `gPath` (`0 → 1`) with two bits: `F 1 = {0}`, `F 0 = σ 1` (bitwise copy).
Least and greatest fixpoint: `{0}` for both functions (`seedCopyFix`). -/
def seedCopyT : Transfer 2 2 :=
  disjT (fun f i => decide (f.val = 1 ∧ i.val = 0))
    (fun f i g j => decide (f.val = 0 ∧ g.val = 1 ∧ j = i))

/-- `{0}` for both functions: the unique fixpoint of `seedCopyT`. -/
def seedCopyFix : Summ 2 2 := fun _ i => decide (i.val = 0)
/-- `σ 0 = {0, 1}`, `σ 1 = {0}`: a prefixpoint of `seedCopyT` strictly between its least
fixpoint and `top`. -/
def seedCopyPre : Summ 2 2 := fun f i => decide (i.val = 0 ∨ f.val = 0)
/-- `σ 0 = ∅`, `σ 1 = {0}`: a postfixpoint of `seedCopyT` strictly between `bot` and its
greatest fixpoint. -/
def seedCopyPost : Summ 2 2 := fun f i => decide (f.val = 1 ∧ i.val = 0)

theorem botT_monotone {n m : Nat} : Monotone (botT (n := n) (m := m)) :=
  fun _ _ _ => Le.refl _

theorem seedCopyT_monotone : Monotone seedCopyT := disjT_monotone _ _
theorem seedCopyT_respectsCalls : RespectsCalls gPath seedCopyT :=
  disjT_respectsCalls (by decide)

theorem not_monotone_nmLfpT : ¬ Monotone nmLfpT := by
  intro h
  have := h bot only0 (bot_le _) 0 0 (by decide)
  revert this; decide

theorem not_monotone_nmGfpT : ¬ Monotone nmGfpT := by
  intro h
  have := h only1 top (le_top _) 0 0 (by decide)
  revert this; decide

theorem not_monotone_nmRankT : ¬ Monotone nmRankT := by
  intro h
  have := h bot only0 (bot_le _) 0 0 (by decide)
  revert this; decide

theorem summ12_ext {τ : Summ 1 2} {P : Bool → Bool → Prop}
    (h : P (τ 0 0) (τ 0 1)) (hall : ∀ a b, P a b → a = true ∧ b = true) : Le top τ := by
  obtain ⟨h0, h1⟩ := hall _ _ h
  intro ⟨f, hf⟩ ⟨i, hi⟩ _
  have hf0 : f = 0 := by omega
  subst hf0
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1

theorem summ12_ext_bot {τ : Summ 1 2} {P : Bool → Bool → Prop}
    (h : P (τ 0 0) (τ 0 1)) (hall : ∀ a b, P a b → a = false ∧ b = false) : Le τ bot := by
  obtain ⟨h0, h1⟩ := hall _ _ h
  intro ⟨f, hf⟩ ⟨i, hi⟩ hτ
  have hf0 : f = 0 := by omega
  subst hf0
  match i, hi with
  | 0, _ => exact absurd hτ (by simp [h0])
  | 1, _ => exact absurd hτ (by simp [h1])

theorem isLeastFixpoint_nmLfpT_top : IsLeastFixpoint nmLfpT top := by
  refine ⟨by decide, fun τ hτ => ?_⟩
  have e0 := congrFun (congrFun hτ 0) 0
  have e1 := congrFun (congrFun hτ 0) 1
  simp only [nmLfpT] at e0 e1
  exact summ12_ext (P := fun a b => (!(a && !b)) = a ∧ (!(a && !b)) = b) ⟨e0, e1⟩
    (by decide)

theorem isGreatestFixpoint_nmGfpT_bot : IsGreatestFixpoint nmGfpT bot := by
  refine ⟨by decide, fun τ hτ => ?_⟩
  have e0 := congrFun (congrFun hτ 0) 0
  have e1 := congrFun (congrFun hτ 0) 1
  simp only [nmGfpT] at e0 e1
  exact summ12_ext_bot (P := fun a b => (!a && b) = a ∧ (!a && b) = b) ⟨e0, e1⟩ (by decide)

theorem isLeastFixpoint_nmRankT_top : IsLeastFixpoint nmRankT top := by
  refine ⟨by decide, fun τ hτ => ?_⟩
  have e0 : (!τ 0 0 || τ 0 1) = τ 0 0 := congrFun (congrFun hτ 0) 0
  exact summ12_ext (P := fun a b => (!a || b) = a) e0 (by decide)

theorem isLeastFixpoint_seedCopyT : IsLeastFixpoint seedCopyT seedCopyFix := by
  have h := isLeastFixpoint_of_iter_fixed seedCopyT_monotone (k := 2) (by decide)
  have e : iter seedCopyT 2 bot = seedCopyFix := by decide
  rw [e] at h; exact h

theorem isGreatestFixpoint_seedCopyT : IsGreatestFixpoint seedCopyT seedCopyFix := by
  have h := isGreatestFixpoint_of_iter_fixed seedCopyT_monotone (k := 2) (by decide)
  have e : iter seedCopyT 2 top = seedCopyFix := by decide
  rw [e] at h; exact h

/-! ## Card `kleene-bound`: Kleene iteration reaches the extremal fixpoints within the height -/

/-- For monotone `F`, the Kleene iterate from `bot` after `n * m` rounds is fixed
(counting argument on set bits; fully proved helper). -/
theorem iter_bot_fixed_at_height {n m : Nat} {F : Transfer n m} (hmono : Monotone F) :
    F (iter F (n * m) bot) = iter F (n * m) bot := by
  have inv : ∀ k, F (iter F k bot) = iter F k bot ∨ k ≤ bitCount (iter F k bot) := by
    intro k
    induction k with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ k ih =>
        by_cases hfix : F (iter F k bot) = iter F k bot
        · left; rw [iter_succ', hfix]; exact hfix
        · right
          have hk := ih.resolve_left hfix
          have hlt := bitCount_lt_of_le_of_ne (iter_bot_le_succ hmono k)
            (by rw [iter_succ']; exact fun e => hfix e.symm)
          omega
  apply Classical.byContradiction
  intro hfix
  have hk := (inv (n * m)).resolve_left hfix
  have hlt := bitCount_lt_of_le_of_ne (iter_bot_le_succ hmono (n * m))
    (by rw [iter_succ']; exact fun e => hfix e.symm)
  have hle := bitCount_le (iter F (n * m + 1) bot)
  omega

/-- For monotone `F`, the Kleene iterate from `top` after `n * m` rounds is fixed. -/
theorem iter_top_fixed_at_height {n m : Nat} {F : Transfer n m} (hmono : Monotone F) :
    F (iter F (n * m) top) = iter F (n * m) top := by
  have inv : ∀ k, F (iter F k top) = iter F k top ∨ k + bitCount (iter F k top) ≤ n * m := by
    intro k
    induction k with
    | zero => exact Or.inr (by have := bitCount_le (top : Summ n m); simp only [iter]; omega)
    | succ k ih =>
        by_cases hfix : F (iter F k top) = iter F k top
        · left; rw [iter_succ', hfix]; exact hfix
        · right
          have hk := ih.resolve_left hfix
          have hlt := bitCount_lt_of_le_of_ne (iter_top_succ_le hmono k)
            (by rw [iter_succ']; exact hfix)
          omega
  apply Classical.byContradiction
  intro hfix
  have hk := (inv (n * m)).resolve_left hfix
  have hlt := bitCount_lt_of_le_of_ne (iter_top_succ_le hmono (n * m))
    (by rw [iter_succ']; exact hfix)
  omega

/-- For monotone `F`, `fuel ≥ n * m` rounds of Kleene iteration from `bot` give the least
fixpoint (`n * m` is the height of the summary lattice). -/
theorem iter_bot_isLeastFixpoint_of_monotone_of_height_le {n m : Nat} {F : Transfer n m}
    (hmono : Monotone F) {fuel : Nat} (hfuel : n * m ≤ fuel) :
    IsLeastFixpoint F (iter F fuel bot) := by
  have hfix := iter_bot_fixed_at_height hmono
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [iter_fixed_add hfix j]
  exact isLeastFixpoint_of_iter_fixed hmono hfix

/-- For monotone `F`, `fuel ≥ n * m` rounds of Kleene iteration from `top` give the
greatest fixpoint. -/
theorem iter_top_isGreatestFixpoint_of_monotone_of_height_le {n m : Nat} {F : Transfer n m}
    (hmono : Monotone F) {fuel : Nat} (hfuel : n * m ≤ fuel) :
    IsGreatestFixpoint F (iter F fuel top) := by
  have hfix := iter_top_fixed_at_height hmono
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [iter_fixed_add hfix j]
  exact isGreatestFixpoint_of_iter_fixed hmono hfix

theorem kleeneLfp_tight_monotone :
    1 * 1 ≤ 1 ∧ ¬ Monotone negT ∧ ¬ IsLeastFixpoint negT (iter negT 1 bot) :=
  ⟨by decide, not_monotone_negT, fun h => negT_no_fixpoint _ h.1⟩

theorem kleeneLfp_tight_fuel :
    Monotone chainLfpT ∧ ¬ (2 * 1 ≤ 1) ∧ ¬ IsLeastFixpoint chainLfpT (iter chainLfpT 1 bot) :=
  ⟨chainLfpT_monotone, by decide, fun h => absurd h.1 (by decide)⟩

theorem kleeneGfp_tight_monotone :
    1 * 1 ≤ 1 ∧ ¬ Monotone negT ∧ ¬ IsGreatestFixpoint negT (iter negT 1 top) :=
  ⟨by decide, not_monotone_negT, fun h => negT_no_fixpoint _ h.1⟩

theorem kleeneGfp_tight_fuel :
    Monotone chainGfpT ∧ ¬ (2 * 1 ≤ 1) ∧
      ¬ IsGreatestFixpoint chainGfpT (iter chainGfpT 1 top) :=
  ⟨chainGfpT_monotone, by decide, fun h => absurd h.1 (by decide)⟩

/-- Non-vacuity at the height `n * m = 4` with two bits per function. -/
theorem kleene_nonvacuous :
    Monotone seedCopyT ∧ 2 * 2 ≤ 4 ∧ iter seedCopyT 4 bot = seedCopyFix ∧
      iter seedCopyT 4 top = seedCopyFix ∧ iter seedCopyT 1 bot ≠ seedCopyFix ∧
      iter seedCopyT 1 top ≠ seedCopyFix :=
  ⟨seedCopyT_monotone, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Card `bottomup-one-sided`: any partition, any order, any fuel errs only one way -/

/-- For monotone `F`, the single-pass bottom-up least computation stays below every
prefixpoint (hence below the least fixpoint), for every decomposition, every order and
every fuel. -/
theorem bottomUpLfp_le_of_monotone_of_prefixpoint {n m k : Nat} {F : Transfer n m}
    (hmono : Monotone F) {τ : Summ n m} (hpre : Le (F τ) τ) (comp : Fin n → Fin k)
    (order : List (Fin k)) (fuel : Nat) : Le (bottomUpLfp F comp order fuel) τ := by
  have step : ∀ (σ : Summ n m) (c : Fin k), Le σ τ →
      Le (solveBlock F comp fuel true c σ) τ := by
    intro σ c hσ
    apply iter_le_of_prefixpoint (blockOp_monotone hmono comp c σ)
    · intro f i hf; simp only [blockInit] at hf; split at hf
      · simp at hf
      · exact hσ f i hf
    · intro f i hf; simp only [blockOp] at hf; split at hf
      · exact hpre f i hf
      · exact hσ f i hf
  suffices ∀ (xs : List (Fin k)) (σ : Summ n m), Le σ τ →
      Le (bottomUp F comp (fun _ => true) xs fuel σ) τ from this order bot (bot_le τ)
  intro xs
  induction xs with
  | nil => intro σ hσ; exact hσ
  | cons c rest ih => intro σ hσ; exact ih _ (step σ c hσ)

/-- For monotone `F`, the single-pass bottom-up greatest computation stays above every
postfixpoint (hence above the greatest fixpoint), for every decomposition, order, fuel. -/
theorem le_bottomUpGfp_of_monotone_of_postfixpoint {n m k : Nat} {F : Transfer n m}
    (hmono : Monotone F) {τ : Summ n m} (hpost : Le τ (F τ)) (comp : Fin n → Fin k)
    (order : List (Fin k)) (fuel : Nat) : Le τ (bottomUpGfp F comp order fuel) := by
  have step : ∀ (σ : Summ n m) (c : Fin k), Le τ σ →
      Le τ (solveBlock F comp fuel false c σ) := by
    intro σ c hσ
    apply le_iter_of_postfixpoint (blockOp_monotone hmono comp c σ)
    · intro f i hf; simp only [blockInit]; split
      · rfl
      · exact hσ f i hf
    · intro f i hf; simp only [blockOp]; split
      · exact hpost f i hf
      · exact hσ f i hf
  suffices ∀ (xs : List (Fin k)) (σ : Summ n m), Le τ σ →
      Le τ (bottomUp F comp (fun _ => false) xs fuel σ) from this order top (le_top τ)
  intro xs
  induction xs with
  | nil => intro σ hσ; exact hσ
  | cons c rest ih => intro σ hσ; exact ih _ (step σ c hσ)

theorem oneSidedLfp_tight_monotone :
    ¬ Monotone nmLfpT ∧ Le (nmLfpT only0) only0 ∧
      ¬ Le (bottomUpLfp nmLfpT oneComp [0] 1) only0 :=
  ⟨not_monotone_nmLfpT, by decide, by decide⟩

theorem oneSidedLfp_tight_prefixpoint :
    Monotone (topT (n := 1) (m := 1)) ∧ ¬ Le (topT (bot : Summ 1 1)) bot ∧
      ¬ Le (bottomUpLfp (topT (n := 1) (m := 1)) oneComp [0] 1) bot :=
  ⟨topT_monotone, by decide, by decide⟩

theorem oneSidedGfp_tight_monotone :
    ¬ Monotone nmGfpT ∧ Le only1 (nmGfpT only1) ∧
      ¬ Le only1 (bottomUpGfp nmGfpT oneComp [0] 1) :=
  ⟨not_monotone_nmGfpT, by decide, by decide⟩

theorem oneSidedGfp_tight_postfixpoint :
    Monotone (botT (n := 1) (m := 1)) ∧ ¬ Le (top : Summ 1 1) (botT top) ∧
      ¬ Le top (bottomUpGfp (botT (n := 1) (m := 1)) oneComp [0] 1) :=
  ⟨botT_monotone, by decide, by decide⟩

/-- Non-vacuity with non-trivial bounds: a prefixpoint other than `top` and a postfixpoint
other than `bot`, exercised at the caller-first order `[0, 1]` of `0 → 1`, where the
single-pass results are not fixpoints (the least result is strictly below the least
fixpoint, the greatest result strictly above the greatest fixpoint). -/
theorem oneSided_nonvacuous :
    Monotone seedCopyT ∧ Le (seedCopyT seedCopyPre) seedCopyPre ∧ seedCopyPre ≠ top ∧
      Le seedCopyPost (seedCopyT seedCopyPost) ∧ seedCopyPost ≠ bot ∧
      ¬ CalleesFirst gPath idComp [0, 1] ∧
      bottomUpLfp seedCopyT idComp [0, 1] 4 ≠ seedCopyFix ∧
      Le (bottomUpLfp seedCopyT idComp [0, 1] 4) seedCopyFix ∧
      bottomUpGfp seedCopyT idComp [0, 1] 4 ≠ seedCopyFix ∧
      Le seedCopyFix (bottomUpGfp seedCopyT idComp [0, 1] 4) :=
  ⟨seedCopyT_monotone, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-! ## Card `prefix-postfix-sound`: checking untrusted summaries one-sidedly -/

/-- For monotone `F`, every prefixpoint (`F σ ≤ σ`) is above the least fixpoint. -/
theorem le_of_monotone_of_isLeastFixpoint_of_prefixpoint {n m : Nat} {F : Transfer n m}
    (hmono : Monotone F) {μ σ : Summ n m} (hμ : IsLeastFixpoint F μ) (hpre : Le (F σ) σ) :
    Le μ σ := by
  classical
  let m₀ : Summ n m := fun f i => decide (∀ ρ, Le (F ρ) ρ → ρ f i = true)
  have hm_le : ∀ ρ, Le (F ρ) ρ → Le m₀ ρ := fun ρ hρ f i hm => (of_decide_eq_true hm) ρ hρ
  have hFm_le : Le (F m₀) m₀ := fun f i hfm =>
    decide_eq_true fun ρ hρ => hρ f i (hmono m₀ ρ (hm_le ρ hρ) f i hfm)
  have hm_fix : F m₀ = m₀ := Le.antisymm hFm_le (hm_le (F m₀) (hmono (F m₀) m₀ hFm_le))
  exact (hμ.2 m₀ hm_fix).trans (hm_le σ hpre)

/-- For monotone `F`, every postfixpoint (`σ ≤ F σ`) is below the greatest fixpoint. -/
theorem le_of_monotone_of_isGreatestFixpoint_of_postfixpoint {n m : Nat} {F : Transfer n m}
    (hmono : Monotone F) {ν σ : Summ n m} (hν : IsGreatestFixpoint F ν) (hpost : Le σ (F σ)) :
    Le σ ν := by
  classical
  let m₀ : Summ n m := fun f i => decide (∃ ρ, Le ρ (F ρ) ∧ ρ f i = true)
  have hle_m : ∀ ρ, Le ρ (F ρ) → Le ρ m₀ := fun ρ hρ f i h => decide_eq_true ⟨ρ, hρ, h⟩
  have hm_le_Fm : Le m₀ (F m₀) := fun f i hm => by
    obtain ⟨ρ, hρ, hρfi⟩ := of_decide_eq_true hm
    exact hmono ρ m₀ (hle_m ρ hρ) f i (hρ f i hρfi)
  have hm_fix : F m₀ = m₀ := Le.antisymm (hle_m (F m₀) (hmono m₀ (F m₀) hm_le_Fm)) hm_le_Fm
  exact (hle_m σ hpost).trans (hν.2 m₀ hm_fix)

theorem prefixSound_tight_monotone :
    ¬ Monotone nmLfpT ∧ IsLeastFixpoint nmLfpT top ∧ Le (nmLfpT only0) only0 ∧
      ¬ Le top only0 :=
  ⟨not_monotone_nmLfpT, isLeastFixpoint_nmLfpT_top, by decide, by decide⟩

theorem postfixSound_tight_monotone :
    ¬ Monotone nmGfpT ∧ IsGreatestFixpoint nmGfpT bot ∧ Le only1 (nmGfpT only1) ∧
      ¬ Le only1 bot :=
  ⟨not_monotone_nmGfpT, isGreatestFixpoint_nmGfpT_bot, by decide, by decide⟩

/-- Tightness of `hμ`: a fixpoint that is not the least one need not lie below a prefixpoint. -/
theorem prefixSound_tight_least :
    Monotone idT ∧ ¬ IsLeastFixpoint idT top ∧ Le (idT bot) bot ∧ ¬ Le (top : Summ 1 1) bot :=
  ⟨idT_monotone, not_isLeastFixpoint_idT_top, by decide, by decide⟩

/-- Tightness of `hpre`: the least fixpoint need not lie below an arbitrary vector. -/
theorem prefixSound_tight_prefixpoint :
    Monotone chainLfpT ∧ IsLeastFixpoint chainLfpT top ∧ ¬ Le (chainLfpT bot) bot ∧
      ¬ Le (top : Summ 2 1) bot :=
  ⟨chainLfpT_monotone, isLeastFixpoint_chainLfpT_top, by decide, by decide⟩

/-- Tightness of `hν`: a fixpoint that is not the greatest one need not lie above a
postfixpoint. -/
theorem postfixSound_tight_greatest :
    Monotone idT ∧ ¬ IsGreatestFixpoint idT bot ∧ Le top (idT top) ∧ ¬ Le (top : Summ 1 1) bot :=
  ⟨idT_monotone, not_isGreatestFixpoint_idT_bot, by decide, by decide⟩

/-- Tightness of `hpost`: an arbitrary vector need not lie below the greatest fixpoint. -/
theorem postfixSound_tight_postfixpoint :
    Monotone chainGfpT ∧ IsGreatestFixpoint chainGfpT bot ∧ ¬ Le top (chainGfpT top) ∧
      ¬ Le (top : Summ 2 1) bot :=
  ⟨chainGfpT_monotone, isGreatestFixpoint_chainGfpT_bot, by decide, by decide⟩

/-- Non-vacuity with non-trivial bounds: the least fixpoint is not `bot`, the prefixpoint is
strictly between it and `top`; the greatest fixpoint is not `top`, the postfixpoint is
strictly between `bot` and it. -/
theorem prefixPostfixSound_nonvacuous :
    Monotone seedCopyT ∧ IsLeastFixpoint seedCopyT seedCopyFix ∧
      Le (seedCopyT seedCopyPre) seedCopyPre ∧ seedCopyFix ≠ bot ∧
      seedCopyPre ≠ seedCopyFix ∧ seedCopyPre ≠ top ∧
      IsGreatestFixpoint seedCopyT seedCopyFix ∧ Le seedCopyPost (seedCopyT seedCopyPost) ∧
      seedCopyFix ≠ top ∧ seedCopyPost ≠ seedCopyFix ∧ seedCopyPost ≠ bot :=
  ⟨seedCopyT_monotone, isLeastFixpoint_seedCopyT, by decide, by decide, by decide, by decide,
    isGreatestFixpoint_seedCopyT, by decide, by decide, by decide, by decide⟩

/-! ## Card `checks-not-exact`: passing both checks does not pin down an extremal fixpoint -/

/-- For the identity equation of one self-recursive function, `top` and `bot` both pass
the prefixpoint and the postfixpoint check (both are fixpoints), yet `top` is not the
least fixpoint and `bot` is not the greatest. -/
theorem prefix_and_postfix_checks_pass_but_not_extremal :
    Monotone idT ∧ RespectsCalls gLoop idT ∧
      (Le (idT top) top ∧ Le top (idT top) ∧ ¬ IsLeastFixpoint idT top) ∧
      (Le (idT bot) bot ∧ Le bot (idT bot) ∧ ¬ IsGreatestFixpoint idT bot) :=
  ⟨idT_monotone, idT_respectsCalls, ⟨by decide, by decide, not_isLeastFixpoint_idT_top⟩,
    ⟨by decide, by decide, not_isGreatestFixpoint_idT_bot⟩⟩

/-! ## Cards `ranked-cert` and `ranked-cert-complete`: exact least-fixpoint certificates -/

/-- The part of `σ` whose bits have rank strictly below `k`. -/
def below {n m : Nat} (σ : Summ n m) (r : Fin n → Fin m → Nat) (k : Nat) : Summ n m :=
  fun f i => σ f i && decide (r f i < k)

/-- A ranking certificate for `σ`: every set bit of `σ` is produced by one application of
`F` to the strictly lower-ranked part of `σ`.  This is a well-founded derivation witness;
checking it evaluates `F` on the vectors `below σ r k`, one per distinct rank value `k`
of a set bit. -/
def RankedJustified {n m : Nat} (F : Transfer n m) (σ : Summ n m)
    (r : Fin n → Fin m → Nat) : Prop :=
  ∀ f i, σ f i = true → F (below σ r (r f i)) f i = true

instance {n m : Nat} (F : Transfer n m) (σ : Summ n m) (r : Fin n → Fin m → Nat) :
    Decidable (RankedJustified F σ r) :=
  inferInstanceAs (Decidable (∀ f i, σ f i = true → F (below σ r (r f i)) f i = true))

/-- The canonical ranking: `kleeneRank F f i` is the least `k < n * m` such that bit `(f, i)`
is set in the Kleene iterate `F^(k+1)(bot)` (that is, after `k + 1` rounds), and `0` if
there is no such `k` (in particular for bits that are never set). -/
def kleeneRank {n m : Nat} (F : Transfer n m) (f : Fin n) (i : Fin m) : Nat :=
  ((List.range (n * m)).find? fun k => iter F (k + 1) bot f i).getD 0

-- `RankedJustified`: positive and negative examples.
example : RankedJustified chainLfpT top (fun f _ => if f.val = 1 then 0 else 1) := by decide
example : ¬ RankedJustified chainLfpT top (fun _ _ => 0) := by decide
example : ¬ RankedJustified idT top (fun _ _ => 0) := by decide
example : kleeneRank chainLfpT 0 0 = 1 ∧ kleeneRank chainLfpT 1 0 = 0 := by decide

/-- No ranking whatsoever justifies the self-supporting fact of `idT` at `top`. -/
theorem not_rankedJustified_idT_top (r : Fin 1 → Fin 1 → Nat) : ¬ RankedJustified idT top r := by
  intro h
  have := h 0 0 rfl
  simp [idT, disjT, below, top] at this

/-- `kleeneRank` is always below the height `n * m` (fully proved). -/
theorem kleeneRank_lt_height {n m : Nat} (F : Transfer n m) (f : Fin n) (i : Fin m) :
    kleeneRank F f i < n * m := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le f.val) f.isLt
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hpos : 0 < n * m := Nat.mul_pos hn hm
  unfold kleeneRank
  cases h : (List.range (n * m)).find? (fun k => iter F (k + 1) bot f i) with
  | none => exact hpos
  | some k =>
    simp only [Option.getD_some]
    exact List.mem_range.mp (List.mem_of_find?_eq_some h)

/-- For monotone `F`, a prefixpoint with a ranking certificate is the least fixpoint. -/
theorem isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified {n m : Nat}
    {F : Transfer n m} (hmono : Monotone F) {σ : Summ n m} {r : Fin n → Fin m → Nat}
    (hpre : Le (F σ) σ) (hrank : RankedJustified F σ r) : IsLeastFixpoint F σ := by
  have hbelow_le : ∀ k, Le (below σ r k) σ := by
    intro k f i h; simp [below] at h; exact h.1
  have hpost : Le σ (F σ) := fun f i h => hmono _ _ (hbelow_le (r f i)) f i (hrank f i h)
  refine ⟨Le.antisymm hpre hpost, fun τ hτ => ?_⟩
  have key : ∀ k, ∀ f i, r f i = k → σ f i = true → τ f i = true := fun k =>
    Nat.strongRecOn k fun k ih f i hr hσ => by
      have h1 : F (below σ r k) f i = true := hr ▸ hrank f i hσ
      have hle : Le (below σ r k) τ := by
        intro g j hgj
        simp only [below, Bool.and_eq_true, decide_eq_true_eq] at hgj
        exact ih (r g j) hgj.2 g j rfl hgj.1
      have h2 := hmono _ _ hle f i h1
      rwa [hτ] at h2
  intro f i hσ
  exact key (r f i) f i rfl hσ

theorem rankedCert_tight_monotone :
    ¬ Monotone negT ∧ Le (negT top) top ∧ RankedJustified negT top (fun _ _ => 0) ∧
      ¬ IsLeastFixpoint negT top :=
  ⟨not_monotone_negT, by decide, by decide, fun h => negT_no_fixpoint _ h.1⟩

theorem rankedCert_tight_prefixpoint :
    Monotone (topT (n := 1) (m := 1)) ∧ ¬ Le (topT (bot : Summ 1 1)) bot ∧
      RankedJustified (topT (n := 1) (m := 1)) bot (fun _ _ => 0) ∧
      ¬ IsLeastFixpoint (topT (n := 1) (m := 1)) bot :=
  ⟨topT_monotone, by decide, by decide, fun h => absurd h.1 (by decide)⟩

/-- Tightness of `hrank`: `top` is a prefixpoint of `idT` that no ranking justifies, and it is
not the least fixpoint. -/
theorem rankedCert_tight_ranking :
    Monotone idT ∧ Le (idT top) top ∧ (∀ r, ¬ RankedJustified idT top r) ∧
      ¬ IsLeastFixpoint idT top :=
  ⟨idT_monotone, by decide, not_rankedJustified_idT_top, not_isLeastFixpoint_idT_top⟩

theorem rankedCert_nonvacuous :
    Monotone chainLfpT ∧ Le (chainLfpT top) top ∧
      RankedJustified chainLfpT top (fun f _ => if f.val = 1 then 0 else 1) :=
  ⟨chainLfpT_monotone, by decide, by decide⟩

/-- Completeness: for monotone `F`, the least fixpoint `μ` carries a complete ranking
certificate: it is a prefixpoint, it is ranked-justified by `kleeneRank F`, and all
these ranks are below the height `n * m`. -/
theorem prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint
    {n m : Nat} {F : Transfer n m} (hmono : Monotone F) {μ : Summ n m}
    (hμ : IsLeastFixpoint F μ) :
    Le (F μ) μ ∧ RankedJustified F μ (kleeneRank F) ∧ ∀ f i, kleeneRank F f i < n * m := by
  refine ⟨by rw [hμ.1]; exact Le.refl μ, ?_, kleeneRank_lt_height F⟩
  have hkleene : IsLeastFixpoint F (iter F (n * m) bot) :=
    iter_bot_isLeastFixpoint_of_monotone_of_height_le hmono (Nat.le_refl _)
  have heq_μ : μ = iter F (n * m) bot :=
    Le.antisymm (hμ.2 _ hkleene.1) (hkleene.2 _ hμ.1)
  intro f i hμfi
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le f.val) f.isLt
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hpos : 0 < n * m := Nat.mul_pos hn hm
  have hex : ∃ k ∈ List.range (n * m), iter F (k + 1) bot f i = true := by
    refine ⟨n * m - 1, List.mem_range.mpr (by omega), ?_⟩
    have hsucc : n * m - 1 + 1 = n * m := by omega
    rw [hsucc, ← heq_μ]; exact hμfi
  have hsome : ∃ k, (List.range (n * m)).find? (fun k => iter F (k + 1) bot f i) = some k := by
    cases hf : (List.range (n * m)).find? (fun k => iter F (k + 1) bot f i) with
    | some k => exact ⟨k, rfl⟩
    | none =>
      obtain ⟨k, hkm, hkt⟩ := hex
      exact absurd hkt (by simpa using List.find?_eq_none.mp hf k hkm)
  obtain ⟨k, hk⟩ := hsome
  have hrk : kleeneRank F f i = k := by simp [kleeneRank, hk]
  have hk_true : iter F (k + 1) bot f i = true :=
    List.find?_some (p := fun k => iter F (k + 1) bot f i) hk
  have hk_mem : k < n * m := List.mem_range.mp (List.mem_of_find?_eq_some hk)
  rw [hrk]
  have hle : Le (iter F k bot) (below μ (kleeneRank F) k) := by
    intro g j hgj
    have hμgj : μ g j = true := by
      rw [heq_μ]
      exact iter_bot_mono hmono (Nat.le_of_lt hk_mem) g j hgj
    cases k with
    | zero => simp [iter, bot] at hgj
    | succ k' =>
      have hex' : ∃ t ∈ List.range (n * m), iter F (t + 1) bot g j = true :=
        ⟨k', List.mem_range.mpr (by omega), hgj⟩
      cases hfg : (List.range (n * m)).find? (fun t => iter F (t + 1) bot g j) with
      | none =>
        obtain ⟨t, htm, htt⟩ := hex'
        exact absurd htt (by simpa using List.find?_eq_none.mp hfg t htm)
      | some t =>
        have ht_le : t ≤ k' := by
          by_cases hle' : t ≤ k'
          · exact hle'
          · exfalso
            have hfalse : iter F (k' + 1) bot g j = false := by
              obtain ⟨_, as, bs, hrange, hnot⟩ :=
                (List.find?_eq_some_iff_append (p := fun t => iter F (t + 1) bot g j)).mp hfg
              have hlen : as.length = t := by
                have hsz := congrArg List.length hrange
                simp at hsz
                have h1 := congrArg (·[as.length]?) hrange
                rw [List.getElem?_range (by omega)] at h1
                simp at h1
                exact h1
              have hk_in_as : k' ∈ as := by
                have h1 := congrArg (·[k']?) hrange
                rw [List.getElem?_range (by omega), List.getElem?_append_left (by omega)] at h1
                exact List.mem_of_getElem? h1.symm
              simpa using hnot k' hk_in_as
            exact absurd hgj (by simp [hfalse])
        simp only [below, kleeneRank, hfg, Option.getD_some, hμgj, Bool.true_and,
          decide_eq_true_eq]
        omega
  rw [iter_succ'] at hk_true
  exact hmono _ _ hle f i hk_true

theorem rankedComplete_tight_monotone :
    ¬ Monotone nmRankT ∧ IsLeastFixpoint nmRankT top ∧
      ¬ (Le (nmRankT top) top ∧ RankedJustified nmRankT top (kleeneRank nmRankT) ∧
        ∀ f i, kleeneRank nmRankT f i < 1 * 2) :=
  ⟨not_monotone_nmRankT, isLeastFixpoint_nmRankT_top, fun h => absurd h.2.1 (by decide)⟩

/-- Tightness of `hμ`: `top` is a fixpoint of `idT` other than the least one, and no
certificate by `kleeneRank` (indeed by no ranking at all) exists for it. -/
theorem rankedComplete_tight_least :
    Monotone idT ∧ idT top = top ∧ ¬ IsLeastFixpoint idT top ∧
      ¬ (Le (idT top) top ∧ RankedJustified idT top (kleeneRank idT) ∧
        ∀ f i, kleeneRank idT f i < 1 * 1) :=
  ⟨idT_monotone, by decide, not_isLeastFixpoint_idT_top,
    fun h => not_rankedJustified_idT_top _ h.2.1⟩

/-- Non-vacuity with a least fixpoint whose bits need two different ranks. -/
theorem rankedComplete_nonvacuous :
    Monotone chainLfpT ∧ IsLeastFixpoint chainLfpT top ∧
      kleeneRank chainLfpT 1 0 = 0 ∧ kleeneRank chainLfpT 0 0 = 1 :=
  ⟨chainLfpT_monotone, isLeastFixpoint_chainLfpT_top, by decide, by decide⟩

end Toy.Scc
