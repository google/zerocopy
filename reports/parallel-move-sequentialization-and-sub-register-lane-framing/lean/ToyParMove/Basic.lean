/-
Parallel moves over abstract locations: stores, the adopted parallel-move semantics,
well-formedness, and sequential (one-at-a-time) moves.
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

section Defs
variable {Loc V : Type} [DecidableEq Loc]

/-- `upd σ d v` is the store `σ` with location `d` overwritten by the value `v`.
Captures a single register or stack-slot write in a machine state. -/
def upd (σ : Loc → V) (d : Loc) (v : V) : Loc → V :=
  fun l => if l = d then v else σ l

/-- The destinations of a list of moves `(dst, src)`, in list order. -/
def dsts (M : List (Loc × Loc)) : List Loc := M.map Prod.fst

/-- The sources of a list of moves `(dst, src)`, in list order. -/
def srcs (M : List (Loc × Loc)) : List Loc := M.map Prod.snd

/-- First-match source lookup: the source of the first move in `M` whose destination is `l`. -/
def lookupSrc : List (Loc × Loc) → Loc → Option Loc
  | [], _ => none
  | m :: M, l => if l = m.1 then some m.2 else lookupSrc M l

/-- **Parallel-move semantics (the reading this package adopts).** Every destination receives
the *old* value of its source simultaneously; locations that are not destinations keep their
value. When a destination is repeated, the *first* entry in list order is used. This reading
is only intended for well-formed moves (`WellFormed`: pairwise-distinct destinations), where it
coincides with every other order-based reading (see `pmove_eq_pmoveLast_of_functional`).
Captures phi-resolution copies and calling-convention shuffles. -/
def pmove (M : List (Loc × Loc)) (σ : Loc → V) : Loc → V :=
  fun l => match lookupSrc M l with
    | some s => σ s
    | none => σ l

/-- The competing "last entry wins" reading of a parallel move with repeated destinations.
Defined only to exhibit that the two readings disagree on ill-formed moves. -/
def pmoveLast (M : List (Loc × Loc)) (σ : Loc → V) : Loc → V := pmove M.reverse σ

/-- **Well-formedness** of a parallel move: destinations are pairwise distinct
(no location is assigned twice). -/
def WellFormed (M : List (Loc × Loc)) : Prop := (dsts M).Nodup

instance (M : List (Loc × Loc)) : Decidable (WellFormed M) :=
  inferInstanceAs (Decidable (dsts M).Nodup)

/-- **Functionality** of a parallel move: moves with the same destination have the same
source. Strictly weaker than `WellFormed`: exact duplicate entries are allowed. -/
def Functional (M : List (Loc × Loc)) : Prop :=
  ∀ d s₁ s₂, (d, s₁) ∈ M → (d, s₂) ∈ M → s₁ = s₂

/-- One sequential move `m = (dst, src)`: `dst := src`, reading the *current* store. -/
def seqStep (σ : Loc → V) (m : Loc × Loc) : Loc → V := upd σ m.1 (σ m.2)

/-- Left-to-right execution of a list of sequential moves. -/
def runSeq (ms : List (Loc × Loc)) (σ : Loc → V) : Loc → V := ms.foldl seqStep σ

end Defs

/-! ### Basic lemmas -/

section Lemmas
variable {Loc V : Type} [DecidableEq Loc]

@[simp] theorem upd_same (σ : Loc → V) (d : Loc) (v : V) : upd σ d v d = v := by
  simp [upd]

theorem upd_ne (σ : Loc → V) {d l : Loc} (v : V) (h : l ≠ d) : upd σ d v l = σ l := by
  simp [upd, h]

@[simp] theorem runSeq_nil (σ : Loc → V) : runSeq [] σ = σ := rfl

@[simp] theorem runSeq_cons (m : Loc × Loc) (ms : List (Loc × Loc)) (σ : Loc → V) :
    runSeq (m :: ms) σ = runSeq ms (seqStep σ m) := rfl

theorem runSeq_append (ms₁ ms₂ : List (Loc × Loc)) (σ : Loc → V) :
    runSeq (ms₁ ++ ms₂) σ = runSeq ms₂ (runSeq ms₁ σ) := by
  simp [runSeq, List.foldl_append]

@[simp] theorem dsts_nil : dsts ([] : List (Loc × Loc)) = [] := rfl
@[simp] theorem srcs_nil : srcs ([] : List (Loc × Loc)) = [] := rfl
@[simp] theorem dsts_cons (m : Loc × Loc) (M : List (Loc × Loc)) :
    dsts (m :: M) = m.1 :: dsts M := rfl
@[simp] theorem srcs_cons (m : Loc × Loc) (M : List (Loc × Loc)) :
    srcs (m :: M) = m.2 :: srcs M := rfl

theorem mem_dsts {M : List (Loc × Loc)} {l : Loc} : l ∈ dsts M ↔ ∃ s, (l, s) ∈ M := by
  simp [dsts]

theorem mem_srcs {M : List (Loc × Loc)} {l : Loc} : l ∈ srcs M ↔ ∃ d, (d, l) ∈ M := by
  simp [srcs]

theorem length_dsts (M : List (Loc × Loc)) : (dsts M).length = M.length := by simp [dsts]
theorem length_srcs (M : List (Loc × Loc)) : (srcs M).length = M.length := by simp [srcs]

theorem lookupSrc_eq_none_iff {M : List (Loc × Loc)} {l : Loc} :
    lookupSrc M l = none ↔ l ∉ dsts M := by
  induction M with
  | nil => simp [lookupSrc]
  | cons m M ih =>
    by_cases h : l = m.1
    · simp [lookupSrc, h]
    · simp [lookupSrc, h, ih]

theorem mem_of_lookupSrc_eq_some {M : List (Loc × Loc)} {l s : Loc}
    (h : lookupSrc M l = some s) : (l, s) ∈ M := by
  induction M with
  | nil => simp [lookupSrc] at h
  | cons m M ih =>
    by_cases hl : l = m.1
    · simp only [lookupSrc, hl, ite_true, Option.some.injEq] at h
      subst h; subst hl; simp
    · simp only [lookupSrc, hl, ite_false] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem functional_of_wellFormed {M : List (Loc × Loc)} (h : WellFormed M) : Functional M := by
  induction M with
  | nil => intro d s₁ s₂ h₁; simp at h₁
  | cons m M ih =>
    have h' : m.1 ∉ dsts M ∧ WellFormed M := by
      simpa [WellFormed, dsts, List.nodup_cons] using h
    intro d s₁ s₂ h₁ h₂
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · rw [← h₂] at h₁; exact (Prod.mk.inj h₁).2
    · exfalso; apply h'.1; rw [← h₁]; exact mem_dsts.2 ⟨s₂, h₂⟩
    · exfalso; apply h'.1; rw [← h₂]; exact mem_dsts.2 ⟨s₁, h₁⟩
    · exact ih h'.2 d s₁ s₂ h₁ h₂

theorem lookupSrc_of_mem {M : List (Loc × Loc)} (hF : Functional M) {l s : Loc}
    (h : (l, s) ∈ M) : lookupSrc M l = some s := by
  cases hlk : lookupSrc M l with
  | none =>
    exact absurd (mem_dsts.2 ⟨s, h⟩) (lookupSrc_eq_none_iff.1 hlk)
  | some s' =>
    rw [hF l s' s (mem_of_lookupSrc_eq_some hlk) h]

theorem pmove_of_mem {M : List (Loc × Loc)} (hF : Functional M) {l s : Loc}
    (h : (l, s) ∈ M) (σ : Loc → V) : pmove M σ l = σ s := by
  simp [pmove, lookupSrc_of_mem hF h]

theorem pmove_of_not_mem_dsts {M : List (Loc × Loc)} {l : Loc} (h : l ∉ dsts M)
    (σ : Loc → V) : pmove M σ l = σ l := by
  simp [pmove, lookupSrc_eq_none_iff.2 h]

theorem functional_of_perm {M M' : List (Loc × Loc)} (hF : Functional M) (hp : M.Perm M') :
    Functional M' := fun d s₁ s₂ h₁ h₂ =>
  hF d s₁ s₂ (hp.mem_iff.2 h₁) (hp.mem_iff.2 h₂)

/-! ### Moves only relocate values -/

theorem seqStep_comp {W : Type} (f : V → W) (τ : Loc → V) (m : Loc × Loc) :
    seqStep (f ∘ τ) m = f ∘ seqStep τ m := by
  funext l
  simp only [seqStep, upd, Function.comp]
  split <;> rfl

/-- Running plain moves commutes with post-composing the store by any function: plain moves
copy values and never inspect them. -/
theorem runSeq_comp {W : Type} (f : V → W) : ∀ (ms : List (Loc × Loc)) (τ : Loc → V),
    runSeq ms (f ∘ τ) = f ∘ runSeq ms τ
  | [], _ => rfl
  | m :: ms, τ => by rw [runSeq_cons, runSeq_cons, seqStep_comp, runSeq_comp f ms]

/-- The parallel move commutes with post-composing the store by any function. -/
theorem pmove_comp {W : Type} (f : V → W) (M : List (Loc × Loc)) (τ : Loc → V) :
    pmove M (f ∘ τ) = f ∘ pmove M τ := by
  funext l
  simp only [pmove, Function.comp]
  cases lookupSrc M l <;> rfl

/-- A move sequence that realizes `M` at a location `l`, from the identity store on locations,
realizes `M` at `l` from every store. -/
theorem runSeq_eq_pmove_at_of_id {ms M : List (Loc × Loc)} {l : Loc}
    (h : runSeq ms (id : Loc → Loc) l = pmove M id l) (σ : Loc → V) :
    runSeq ms σ l = pmove M σ l := by
  have e1 := congrFun (runSeq_comp σ ms id) l
  have e2 := congrFun (pmove_comp σ M id) l
  simp only [Function.comp_id, Function.comp] at e1 e2
  rw [e1, e2, h]

/-- A move sequence that realizes `M` from the identity store on locations realizes `M` from
every store. -/
theorem runSeq_eq_pmove_of_id {ms M : List (Loc × Loc)}
    (h : runSeq ms (id : Loc → Loc) = pmove M id) (σ : Loc → V) : runSeq ms σ = pmove M σ :=
  funext fun l => runSeq_eq_pmove_at_of_id (congrFun h l) σ

/-- Two locations that every store over a value type with two distinct values maps to the same
value are equal. -/
theorem eq_of_forall_store {x y : Loc} (a b : V) (hab : a ≠ b)
    (h : ∀ σ : Loc → V, σ x = σ y) : x = y := by
  apply Classical.byContradiction
  intro hne
  have := h (fun z => if z = x then a else b)
  simp only [ite_true, show y ≠ x from fun e => hne e.symm, ite_false] at this
  exact hab this

/-- Conversely, over a value type with two distinct values, a move sequence that realizes `M`
at `l` from every store realizes it from the identity store on locations. -/
theorem runSeq_eq_pmove_at_id_of_forall {ms M : List (Loc × Loc)} {l : Loc} (a b : V)
    (hab : a ≠ b) (h : ∀ σ : Loc → V, runSeq ms σ l = pmove M σ l) :
    runSeq ms (id : Loc → Loc) l = pmove M id l := by
  apply eq_of_forall_store a b hab
  intro σ
  have e1 := congrFun (runSeq_comp σ ms id) l
  have e2 := congrFun (pmove_comp σ M id) l
  simp only [Function.comp_id, Function.comp] at e1 e2
  rw [← e1, ← e2]
  exact h σ

/-- Pigeonhole: a duplicate-free list contained in another is no longer than it. -/
theorem length_le_of_nodup_of_subset {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hn, hs => by
    have ha : a ∈ l₂ := hs (List.mem_cons_self ..)
    have hn' := List.nodup_cons.1 hn
    have hsub : t ⊆ l₂.erase a := by
      intro x hx
      have hxa : x ≠ a := fun e => hn'.1 (e ▸ hx)
      exact (List.mem_erase_of_ne hxa).2 (hs (List.mem_cons_of_mem _ hx))
    have := length_le_of_nodup_of_subset hn'.2 hsub
    rw [List.length_erase_of_mem ha] at this
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- Remove duplicates from a list, keeping the last occurrence of each element. -/
def dedupL {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then dedupL l else a :: dedupL l

theorem mem_dedupL {α : Type} [DecidableEq α] {a : α} : ∀ {l : List α}, a ∈ dedupL l ↔ a ∈ l
  | [] => by simp [dedupL]
  | b :: l => by
    by_cases h : b ∈ l
    · simp only [dedupL, h, ite_true, mem_dedupL, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h') <;> assumption
    · simp [dedupL, h, mem_dedupL]

theorem nodup_dedupL {α : Type} [DecidableEq α] : ∀ (l : List α), (dedupL l).Nodup
  | [] => by simp [dedupL]
  | b :: l => by
    by_cases h : b ∈ l
    · simpa [dedupL, h] using nodup_dedupL l
    · simp only [dedupL, h, ↓reduceIte, List.nodup_cons]
      exact ⟨fun h' => h (mem_dedupL.1 h'), nodup_dedupL l⟩

end Lemmas

end Toy.ParMove
