/-
Toy.Scc.BottomUp
================

The bottom-up algorithm: blocks are processed one at a time in a given order; each
block is solved by Kleene iteration of its own equations with all other summaries
held fixed.  Also: hierarchical (per-block extremal) solutions, which describe what
a mixture of least and greatest per-block fixpoints computes, and fully proved
certification helpers and examples.
-/
import Toy.Scc.Lattice

namespace Toy.Scc

/-- The block operator: the equations of block `c` (taken from `F`), with every summary
outside block `c` frozen to its value in `σ`. -/
def blockOp {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (c : Fin k)
    (σ : Summ n m) : Transfer n m :=
  fun τ f => if comp f = c then F τ f else σ f

/-- Starting point of the inner iteration for block `c`: block `c` reset to the empty
set (`least = true`) or to the full set (`least = false`); other blocks from `σ`. -/
def blockInit {n m k : Nat} (comp : Fin n → Fin k) (c : Fin k) (least : Bool)
    (σ : Summ n m) : Summ n m :=
  fun f => if comp f = c then (fun _ => !least) else σ f

/-- Solve block `c` by `fuel` rounds of Kleene iteration of its block operator. -/
def solveBlock {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (fuel : Nat)
    (least : Bool) (c : Fin k) (σ : Summ n m) : Summ n m :=
  iter (blockOp F comp c σ) fuel (blockInit comp c least σ)

/-- The bottom-up algorithm: one pass over `order`, performing one block solve per list
entry (a block listed twice is solved twice), with the least (`sign c = true`) or
greatest (`sign c = false`) inner fixpoint, starting from the summary vector `init`. -/
def bottomUp {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (sign : Fin k → Bool)
    (order : List (Fin k)) (fuel : Nat) (init : Summ n m) : Summ n m :=
  order.foldl (fun σ c => solveBlock F comp fuel (sign c) c σ) init

/-- Bottom-up least fixpoint: every block solved with its least inner fixpoint, start `bot`. -/
def bottomUpLfp {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k)
    (order : List (Fin k)) (fuel : Nat) : Summ n m :=
  bottomUp F comp (fun _ => true) order fuel bot

/-- Bottom-up greatest fixpoint: every block solved with its greatest inner fixpoint,
start `top`. -/
def bottomUpGfp {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k)
    (order : List (Fin k)) (fuel : Nat) : Summ n m :=
  bottomUp F comp (fun _ => false) order fuel top

/-! ## Hierarchical solutions -/

/-- `σ` solves block `c` extremally: restricted to block `c`, `σ` is the least
(`least = true`) or greatest (`least = false`) fixpoint of the block operator whose
frozen outside values are taken from `σ` itself. -/
def BlockExtremal {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (c : Fin k)
    (least : Bool) (σ : Summ n m) : Prop :=
  blockOp F comp c σ σ = σ ∧
    ∀ τ, blockOp F comp c σ τ = τ → (if least then Le σ τ else Le τ σ)

/-- Coordinatewise block-extremality for the sign assignment `sign`: every block `c` is
the least (`sign c = true`) or greatest (`sign c = false`) fixpoint of its own equations
when all other blocks are frozen, as constants, to their values in `σ`.

This is *not* the general semantics of hierarchical (nested) fixpoint equation systems,
such as Boolean equation systems, where blocks are ordered and the solution of an inner
block, as a function of the outer variables, is substituted into the outer blocks.  The
two notions agree when no block depends on a block of a later position (for example
under `CalleesFirst` and `RespectsCalls`); with cyclic dependencies between blocks of
different signs, `HierSolution` can have several solutions
(`hierSolution_swapT_gCycle_mixSign_not_unique`). -/
def HierSolution {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k)
    (sign : Fin k → Bool) (σ : Summ n m) : Prop :=
  ∀ c, BlockExtremal F comp c (sign c) σ

/-- A hierarchical solution is a fixpoint of the whole transfer (fully proved). -/
theorem HierSolution.fixpoint {n m k : Nat} {F : Transfer n m} {comp : Fin n → Fin k}
    {sign : Fin k → Bool} {σ : Summ n m} (h : HierSolution F comp sign σ) : F σ = σ := by
  funext f
  have := congrFun (h (comp f)).1 f
  simpa [blockOp] using this

/-- A hierarchical solution lies between the least and the greatest fixpoint of the whole
transfer, whenever these exist (fully proved; immediate from `HierSolution.fixpoint`). -/
theorem le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint {n m k : Nat}
    {F : Transfer n m} {comp : Fin n → Fin k} {sign : Fin k → Bool} {μ ν σ : Summ n m}
    (hμ : IsLeastFixpoint F μ) (hν : IsGreatestFixpoint F ν)
    (h : HierSolution F comp sign σ) : Le μ σ ∧ Le σ ν :=
  ⟨hμ.2 σ h.fixpoint, hν.2 σ h.fixpoint⟩

/-! ## Certification helpers (fully proved) -/

theorem blockOp_monotone {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    (comp : Fin n → Fin k) (c : Fin k) (σ : Summ n m) : Monotone (blockOp F comp c σ) := by
  intro τ ρ h f i hf
  simp only [blockOp] at hf ⊢
  split at hf
  next hc => simp only [hc, ↓reduceIte]; exact hmono τ ρ h f i hf
  next hc => simp only [hc, ↓reduceIte]; exact hf

theorem blockInit_le_of_fixpoint {n m k : Nat} {F : Transfer n m} {comp : Fin n → Fin k}
    {c : Fin k} {σ τ : Summ n m} (hτ : blockOp F comp c σ τ = τ) :
    Le (blockInit comp c true σ) τ := by
  intro f i hf
  simp only [blockInit] at hf
  split at hf
  next => simp at hf
  next hc => rw [← hτ]; simp only [blockOp, hc, ↓reduceIte]; exact hf

theorem le_blockInit_of_fixpoint {n m k : Nat} {F : Transfer n m} {comp : Fin n → Fin k}
    {c : Fin k} {σ τ : Summ n m} (hτ : blockOp F comp c σ τ = τ) :
    Le τ (blockInit comp c false σ) := by
  intro f i hf
  simp only [blockInit]
  split
  next => rfl
  next hc => rw [← hτ] at hf; simp only [blockOp, hc, ↓reduceIte] at hf; exact hf

/-- If the inner iteration of block `c` lands exactly on `σ` and `σ` is a fixpoint of
its block operator, then `σ` solves block `c` extremally (fully proved). -/
theorem blockExtremal_of_solveBlock_eq {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    {comp : Fin n → Fin k} {c : Fin k} {least : Bool} {fuel : Nat} {σ : Summ n m}
    (hfix : blockOp F comp c σ σ = σ) (heq : solveBlock F comp fuel least c σ = σ) :
    BlockExtremal F comp c least σ := by
  refine ⟨hfix, fun τ hτ => ?_⟩
  have hτ' : Le (blockOp F comp c σ τ) τ := by rw [hτ]; exact Le.refl τ
  have hτ'' : Le τ (blockOp F comp c σ τ) := by rw [hτ]; exact Le.refl τ
  cases least
  · show Le τ σ
    rw [← heq]
    exact le_iter_of_postfixpoint (blockOp_monotone hmono comp c σ)
      (le_blockInit_of_fixpoint hτ) hτ'' fuel
  · show Le σ τ
    rw [← heq]
    exact iter_le_of_prefixpoint (blockOp_monotone hmono comp c σ)
      (blockInit_le_of_fixpoint hτ) hτ' fuel

/-- Decidable certificate for `HierSolution`. -/
def hierCertB {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (sign : Fin k → Bool)
    (fuel : Nat) (σ : Summ n m) : Bool :=
  (List.finRange k).all fun c =>
    summEqB (blockOp F comp c σ σ) σ && summEqB (solveBlock F comp fuel (sign c) c σ) σ

theorem hierSolution_of_hierCertB {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    {comp : Fin n → Fin k} {sign : Fin k → Bool} {fuel : Nat} {σ : Summ n m}
    (h : hierCertB F comp sign fuel σ = true) : HierSolution F comp sign σ := by
  intro c
  simp only [hierCertB, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true, summEqB_eq_true_iff] at h
  exact blockExtremal_of_solveBlock_eq hmono (h c).1 (h c).2

/-! ## Correctness of the bottom-up pass (fully proved helpers) -/

theorem iter_blockOp_outside {n m k : Nat} {F : Transfer n m} {comp : Fin n → Fin k} {c : Fin k}
    {σ x : Summ n m} (hx : ∀ f, comp f ≠ c → x f = σ f) :
    ∀ j f, comp f ≠ c → iter (blockOp F comp c σ) j x f = σ f
  | 0, f, hf => hx f hf
  | j + 1, f, hf => by rw [iter_succ']; simp [blockOp, hf]

/-- Solving block `c` changes nothing outside block `c`. -/
theorem solveBlock_outside {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (fuel : Nat)
    (least : Bool) (c : Fin k) (σ : Summ n m) :
    ∀ f, comp f ≠ c → solveBlock F comp fuel least c σ f = σ f :=
  fun f hf => iter_blockOp_outside (fun g hg => by simp [blockInit, hg]) fuel f hf

theorem blockOp_congr_outside {n m k : Nat} {F : Transfer n m} {comp : Fin n → Fin k}
    {c : Fin k} {σ σ' : Summ n m} (h : ∀ f, comp f ≠ c → σ f = σ' f) :
    blockOp F comp c σ = blockOp F comp c σ' := by
  funext τ f
  by_cases hf : comp f = c
  · simp [blockOp, hf]
  · simp [blockOp, hf, h f hf]

/-- With inner fuel at least the height, solving a block yields a vector that solves that
block extremally. -/
theorem blockExtremal_solveBlock {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    {comp : Fin n → Fin k} {fuel : Nat} (hfuel : n * m ≤ fuel) (least : Bool) (c : Fin k)
    (σ : Summ n m) : BlockExtremal F comp c least (solveBlock F comp fuel least c σ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  have hcongr : blockOp F comp c (solveBlock F comp (n * m + j) least c σ) =
      blockOp F comp c σ :=
    blockOp_congr_outside (fun f hf => solveBlock_outside F comp _ least c σ f hf)
  have hG := blockOp_monotone hmono comp c σ
  unfold BlockExtremal
  rw [hcongr]
  cases least
  · have hx : Le (blockOp F comp c σ (blockInit comp c false σ)) (blockInit comp c false σ) := by
      intro f i _
      simp only [blockInit, blockOp] at *
      split
      · rfl
      · simp_all
    have hfix := iter_fixed_at_height_of_descending (iter_descending_of_prefixpoint hG hx)
    have e : solveBlock F comp (n * m + j) false c σ =
        iter (blockOp F comp c σ) (n * m) (blockInit comp c false σ) := iter_fixed_add hfix j
    rw [e]
    refine ⟨hfix, fun τ hτ => ?_⟩
    show Le τ _
    exact le_iter_of_postfixpoint hG (le_blockInit_of_fixpoint hτ)
      (by rw [hτ]; exact Le.refl τ) _
  · have hx : Le (blockInit comp c true σ) (blockOp F comp c σ (blockInit comp c true σ)) := by
      intro f i hf
      simp only [blockInit, blockOp] at *
      split at hf
      · simp at hf
      · simp_all
    have hfix := iter_fixed_at_height_of_ascending (iter_ascending_of_postfixpoint hG hx)
    have e : solveBlock F comp (n * m + j) true c σ =
        iter (blockOp F comp c σ) (n * m) (blockInit comp c true σ) := iter_fixed_add hfix j
    rw [e]
    refine ⟨hfix, fun τ hτ => ?_⟩
    show Le _ τ
    exact iter_le_of_prefixpoint hG (blockInit_le_of_fixpoint hτ)
      (by rw [hτ]; exact Le.refl τ) _

/-- Re-solving a block that is already solved extremally changes nothing. -/
theorem solveBlock_eq_of_blockExtremal {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    {comp : Fin n → Fin k} {fuel : Nat} (hfuel : n * m ≤ fuel) {least : Bool} {c : Fin k}
    {σ : Summ n m} (h : BlockExtremal F comp c least σ) :
    solveBlock F comp fuel least c σ = σ := by
  have hs := blockExtremal_solveBlock hmono (comp := comp) hfuel least c σ
  have hcongr : blockOp F comp c (solveBlock F comp fuel least c σ) = blockOp F comp c σ :=
    blockOp_congr_outside (fun f hf => solveBlock_outside F comp _ least c σ f hf)
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨h1, h2⟩ := h
  rw [hcongr] at hs1 hs2
  have a := h2 _ hs1
  have b := hs2 σ h1
  cases least
  · simp only [Bool.false_eq_true, ↓reduceIte] at a b; exact Le.antisymm a b
  · simp only [↓reduceIte] at a b; exact Le.antisymm b a

/-- Block-extremality of `c` survives an update of another block `d` that `c` does not
call. -/
theorem blockExtremal_of_update {n m k : Nat} {E : Graph n} {F : Transfer n m}
    (hresp : RespectsCalls E F) {comp : Fin n → Fin k} {c d : Fin k} {least : Bool}
    {σ σ' : Summ n m} (h : BlockExtremal F comp c least σ) (hcd : c ≠ d)
    (hupd : ∀ f, comp f ≠ d → σ' f = σ f)
    (hnocall : ∀ f g, comp f = c → E f g = true → comp g ≠ d) :
    BlockExtremal F comp c least σ' := by
  obtain ⟨h1, h2⟩ := h
  have hFeq : ∀ ρ ρ' : Summ n m, (∀ g, comp g ≠ d → ρ g = ρ' g) → ∀ f, comp f = c →
      F ρ f = F ρ' f := fun ρ ρ' hρ f hf =>
    hresp ρ ρ' f (fun g e => hρ g (hnocall f g hf e))
  refine ⟨?_, fun τ hτ => ?_⟩
  · funext f
    by_cases hf : comp f = c
    · have hfd : comp f ≠ d := hf ▸ hcd
      have e1 := congrFun h1 f
      simp only [blockOp, hf, ↓reduceIte] at e1 ⊢
      rw [hFeq σ' σ hupd f hf, e1, hupd f hfd]
    · simp [blockOp, hf]
  · let τ0 : Summ n m := fun g => if comp g = d then σ g else τ g
    have hτ0 : blockOp F comp c σ τ0 = τ0 := by
      funext f
      by_cases hf : comp f = c
      · have hfd : comp f ≠ d := hf ▸ hcd
        have e1 := congrFun hτ f
        simp only [blockOp, hf, ↓reduceIte] at e1 ⊢
        rw [hFeq τ0 τ (fun g hg => by simp [τ0, hg]) f hf, e1]
        simp [τ0, hfd]
      · have e1 := congrFun hτ f
        simp only [blockOp, hf, ↓reduceIte] at e1 ⊢
        by_cases hfd : comp f = d
        · simp [τ0, hfd]
        · simp only [τ0, hfd, ↓reduceIte]; rw [← e1, hupd f hfd]
    have hext := h2 τ0 hτ0
    have hout : ∀ f, comp f ≠ c → τ f = σ' f := fun f hf => by
      have e1 := congrFun hτ f
      simp only [blockOp, hf, ↓reduceIte] at e1
      exact e1.symm
    cases least
    · simp only [Bool.false_eq_true, ↓reduceIte] at hext ⊢
      intro f i hi
      by_cases hf : comp f = c
      · have hfd : comp f ≠ d := hf ▸ hcd
        rw [hupd f hfd]
        have : τ0 f i = true := by simp [τ0, hfd, hi]
        exact hext f i this
      · rw [← hout f hf]; exact hi
    · simp only [↓reduceIte] at hext ⊢
      intro f i hi
      by_cases hf : comp f = c
      · have hfd : comp f ≠ d := hf ▸ hcd
        rw [hupd f hfd] at hi
        have := hext f i hi
        simpa [τ0, hfd] using this
      · rw [hout f hf]; exact hi

/-- A block with no functions is trivially solved extremally. -/
theorem blockExtremal_of_unused {n m k : Nat} {F : Transfer n m} {comp : Fin n → Fin k}
    {c : Fin k} {least : Bool} {σ : Summ n m} (hunused : ∀ f, comp f ≠ c) :
    BlockExtremal F comp c least σ := by
  have hconst : ∀ τ, blockOp F comp c σ τ = σ := fun τ => by
    funext f; simp [blockOp, hunused f]
  refine ⟨hconst σ, fun τ hτ => ?_⟩
  rw [hconst τ] at hτ
  subst hτ
  cases least <;> exact Le.refl _

/-- Existence half of `bottomup-mixed`: the bottom-up pass computes a hierarchical
solution. -/
theorem hierSolution_bottomUp {n m k : Nat} {E : Graph n} {F : Transfer n m}
    {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat} (hmono : Monotone F)
    (hresp : RespectsCalls E F) (hcover : Covers comp order) (hfirst : CalleesFirst E comp order)
    (hfuel : n * m ≤ fuel) (sign : Fin k → Bool) (init : Summ n m) :
    HierSolution F comp sign (bottomUp F comp sign order fuel init) := by
  have key : ∀ (rest pre : List (Fin k)) (σ : Summ n m), pre ++ rest = order →
      (∀ c ∈ pre, BlockExtremal F comp c (sign c) σ) →
      ∀ c ∈ order, BlockExtremal F comp c (sign c)
        (rest.foldl (fun σ c => solveBlock F comp fuel (sign c) c σ) σ) := by
    intro rest
    induction rest with
    | nil =>
        intro pre σ hpre h c hc
        simp only [List.append_nil] at hpre
        subst hpre
        exact h c hc
    | cons d rest ih =>
        intro pre σ hpre h
        simp only [List.foldl_cons]
        apply ih (pre ++ [d]) _ (by rw [← hpre]; simp)
        intro c hc
        rw [List.mem_append, List.mem_singleton] at hc
        by_cases hd : d ∈ pre
        · rw [solveBlock_eq_of_blockExtremal hmono hfuel (h d hd)]
          rcases hc with hc | rfl
          · exact h c hc
          · exact h _ hd
        · rcases hc with hc | rfl
          · have hcd : c ≠ d := fun e => hd (e ▸ hc)
            refine blockExtremal_of_update hresp (h c hc) hcd
              (fun f hf => solveBlock_outside F comp fuel (sign d) d σ f hf) ?_
            intro f g hf e hg
            have hne : comp f ≠ comp g := by rw [hf, hg]; exact hcd
            have hlt := (hfirst f g e hne).2.2
            rw [hf, hg] at hlt
            have hpd : pos order d = pre.length := by
              rw [← hpre]; unfold pos; rw [List.idxOf_append]; simp [hd]
            have hpc : pos order c < pre.length := by
              rw [← hpre]; unfold pos; rw [List.idxOf_append]; simp only [hc, ↓reduceIte]
              exact List.idxOf_lt_length_of_mem hc
            omega
          · exact blockExtremal_solveBlock hmono hfuel _ _ _
  intro c
  by_cases hc : c ∈ order
  · exact key order [] init (by simp) (by simp) c hc
  · exact blockExtremal_of_unused (fun f e => hc (e ▸ hcover f))

/-- Uniqueness half of `bottomup-mixed`: under `RespectsCalls` and `CalleesFirst`, there is
at most one hierarchical solution. -/
theorem hierSolution_unique {n m k : Nat} {E : Graph n} {F : Transfer n m}
    {comp : Fin n → Fin k} {order : List (Fin k)} (hresp : RespectsCalls E F)
    (hfirst : CalleesFirst E comp order) {sign : Fin k → Bool} {σ σ' : Summ n m}
    (h : HierSolution F comp sign σ) (h' : HierSolution F comp sign σ') : σ = σ' := by
  have key : ∀ p, ∀ c, pos order c = p → ∀ g, comp g = c → σ g = σ' g := by
    intro p
    induction p using Nat.strongRecOn with
    | ind p ih =>
      intro c hp
      -- values on callee blocks agree
      have hcallee : ∀ f g, comp f = c → E f g = true → comp g ≠ c → σ g = σ' g := by
        intro f g hf e hg
        have hlt := (hfirst f g e (by rw [hf]; exact Ne.symm hg)).2.2
        rw [hf, hp] at hlt
        exact ih _ hlt (comp g) rfl g rfl
      let τ : Summ n m := fun g => if comp g = c then σ' g else σ g
      let τ' : Summ n m := fun g => if comp g = c then σ g else σ' g
      have hfix' : ∀ f, comp f = c → F σ' f = σ' f := fun f hf => by
        have := congrFun (h' c).1 f; simpa [blockOp, hf] using this
      have hfix : ∀ f, comp f = c → F σ f = σ f := fun f hf => by
        have := congrFun (h c).1 f; simpa [blockOp, hf] using this
      have hτ : blockOp F comp c σ τ = τ := by
        funext f
        by_cases hf : comp f = c
        · simp only [blockOp, hf, ↓reduceIte, τ]
          rw [← hfix' f hf]
          apply hresp
          intro g e
          by_cases hg : comp g = c
          · simp [hg]
          · simp only [hg, ↓reduceIte]; exact hcallee f g hf e hg
        · simp [blockOp, hf, τ]
      have hτ' : blockOp F comp c σ' τ' = τ' := by
        funext f
        by_cases hf : comp f = c
        · simp only [blockOp, hf, ↓reduceIte, τ']
          rw [← hfix f hf]
          apply hresp
          intro g e
          by_cases hg : comp g = c
          · simp [hg]
          · simp only [hg, ↓reduceIte]; exact (hcallee f g hf e hg).symm
        · simp [blockOp, hf, τ']
      have a := (h c).2 τ hτ
      have b := (h' c).2 τ' hτ'
      intro g hg
      funext i
      cases hs : sign c
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at a b
        have a' := a g i
        have b' := b g i
        simp only [τ, τ', hg, ↓reduceIte] at a' b'
        cases h1 : σ g i <;> cases h2 : σ' g i <;> simp_all
      · simp only [hs, ↓reduceIte] at a b
        have a' := a g i
        have b' := b g i
        simp only [τ, τ', hg, ↓reduceIte] at a' b'
        cases h1 : σ g i <;> cases h2 : σ' g i <;> simp_all
  funext g
  exact key _ (comp g) rfl g rfl

/-! ## Examples -/

-- `bottomUpLfp` / `bottomUpGfp` on `0 → 1` with callees first.
example : bottomUpLfp chainLfpT idComp [1, 0] 2 = top := by decide
example : bottomUpGfp chainGfpT idComp [1, 0] 2 = bot := by decide
-- ... and with the caller first.
example : bottomUpLfp chainLfpT idComp [0, 1] 2 ≠ top := by decide

-- `BlockExtremal` / `HierSolution`: positive and negative examples.
theorem hierSolution_chainLfpT_top : HierSolution chainLfpT idComp (fun _ => true) top :=
  hierSolution_of_hierCertB (fuel := 2) chainLfpT_monotone (by decide)

theorem hierSolution_idT_bot_least : HierSolution idT oneComp (fun _ => true) bot :=
  hierSolution_of_hierCertB (fuel := 1) idT_monotone (by decide)

theorem hierSolution_idT_top_greatest : HierSolution idT oneComp (fun _ => false) top :=
  hierSolution_of_hierCertB (fuel := 1) idT_monotone (by decide)

/-- `top` is a fixpoint of `idT` but not its least-signed hierarchical solution. -/
theorem not_hierSolution_idT_top_least : ¬ HierSolution idT oneComp (fun _ => true) top := by
  intro h
  have := (h 0).2 bot (by decide)
  revert this; decide

/-- Sign assignment on two blocks: block `1` least, block `0` greatest. -/
def mixSign : Fin 2 → Bool := fun c => decide (c.val = 1)

/-- On the 2-cycle: `F 0 = σ 1`, `F 1 = σ 0`. -/
def swapT : Transfer 2 1 := disjT (fun _ _ => false) (fun f _ g _ => decide (f ≠ g))

theorem swapT_monotone : Monotone swapT := disjT_monotone _ _
theorem swapT_respectsCalls : RespectsCalls gCycle swapT := disjT_respectsCalls (by decide)

/-- With a cyclic dependency between a greatest-signed block (`0`) and a least-signed block
(`1`), coordinatewise block-extremality is not unique: both `bot` and `top` are
hierarchical solutions.  (Nested-substitution semantics of the equation system
`ν X₀ = X₁; μ X₁ = X₀`, with `X₀` outermost, has the single solution `top`.) -/
theorem hierSolution_swapT_gCycle_mixSign_not_unique :
    HierSolution swapT idComp mixSign bot ∧ HierSolution swapT idComp mixSign top ∧
      (bot : Summ 2 1) ≠ top :=
  ⟨hierSolution_of_hierCertB (fuel := 2) swapT_monotone (by decide),
    hierSolution_of_hierCertB (fuel := 2) swapT_monotone (by decide), by decide⟩

/-- A summary vector that is not even a fixpoint is never a hierarchical solution. -/
theorem not_hierSolution_chainLfpT_bot (sign : Fin 2 → Bool) :
    ¬ HierSolution chainLfpT idComp sign bot := fun h =>
  absurd h.fixpoint (by decide)

end Toy.Scc
