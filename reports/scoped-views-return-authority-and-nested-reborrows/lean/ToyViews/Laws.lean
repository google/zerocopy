import ToyViews.Basic

/-!
# Structural laws of the loan tree, and write exclusivity

Each law is a separate named `Prop` so that theorems can name exactly the laws they use.
Quantifiers over view ids are bounded by `s.size` and quantifiers over addresses by `s.width`;
both bounds are exact (no view id at or beyond `s.size` exists, and no view covers an address at or
beyond `s.width`, see `isActive_lt_size` and `covers_lt_width`), so the bounded forms say the same
as the unbounded ones while being decidable on concrete states.
-/

namespace Toy.Views

/-! ## Decidability helpers -/

instance decForallEqSome {α : Type} (o : Option α) (P : α → Prop) [DecidablePred P] :
    Decidable (∀ a, o = some a → P a) :=
  match o with
  | none => isTrue (fun _ h => nomatch h)
  | some x =>
    if h : P x then isTrue (fun a ha => by cases ha; exact h)
    else isFalse (fun H => h (H x rfl))

instance decExistsEqSomeSucc (o : Option Nat) : Decidable (∃ d, o = some (d + 1)) :=
  match o with
  | none => isFalse (fun ⟨_, h⟩ => nomatch h)
  | some 0 => isFalse (fun ⟨_, h⟩ => by simp at h)
  | some (n + 1) => isTrue ⟨n, rfl⟩

namespace State

theorem lt_size_of_view?_eq_some {s : State} {v : ViewId} {vw : View} (h : s.view? v = some vw) :
    v < s.size := by
  unfold view? at h; unfold size
  rcases Nat.lt_or_ge v s.views.length with hv | hv
  · exact hv
  · rw [List.getElem?_eq_none hv] at h; simp at h

theorem isActive_lt_size {s : State} {v : ViewId} (h : s.isActive v = true) : v < s.size := by
  unfold isActive at h
  cases hv : s.view? v with
  | none => simp [hv] at h
  | some vw => exact lt_size_of_view?_eq_some hv

theorem lt_size_of_parentOf {s : State} {v p : ViewId} (h : s.parentOf v = some p) :
    v < s.size := by
  unfold parentOf at h
  cases hv : s.view? v with
  | none => simp [hv] at h
  | some vw => exact lt_size_of_view?_eq_some hv

theorem length_le_foldr_max {l : List View} {vw : View} (h : vw ∈ l) :
    vw.cells.length ≤ l.foldr (fun vw m => max vw.cells.length m) 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; omega
    · have := ih h; omega

theorem covers_lt_width {s : State} {v : ViewId} {a : Addr} (h : s.covers v a = true) :
    a < s.width := by
  unfold covers cell? at h
  cases hv : s.view? v with
  | none => simp [hv] at h
  | some vw =>
    simp only [hv, Option.bind_some] at h
    have hmem : vw ∈ s.views := by
      unfold view? at hv; exact List.mem_of_getElem? hv
    have hle : vw.cells.length ≤ s.width := length_le_foldr_max hmem
    unfold View.cell? at h
    rcases Nat.lt_or_ge a vw.cells.length with ha | ha
    · exact Nat.lt_of_lt_of_le ha hle
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha] at h; simp at h

end State

/-! ## The structural laws -/

/-- Every parent link points to an existing view. -/
def ParentsExist (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < s.size

/-- Parents are created before their children: every parent link points to a smaller id. (Implies
`ParentsExist` and acyclicity of the parent relation.) -/
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v

/-- An active view's cells are covered by its parent, and that parent is active: a reborrow never
outlives, or reaches beyond, the view it was taken from. -/
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true

/-- Every cell covered by an active exclusive child is recorded in its parent as loaned to that
child. -/
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)

/-- Every cell covered by an active shared child is held by its parent as an `own` cell of
positive depth (the parent is read-only there while the child reads). -/
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)

/-- Active children of shared views are shared: a read-only view cannot lend exclusively. -/
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared

/-- Depth is a counter: the depth of an active view's accessible cell equals the view's mode
baseline plus the number of active shared children reading that cell. -/
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a

/-- Distinct active root views cover disjoint addresses (each raw-pointer-owned cell has one
owner). -/
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false

set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (ParentsExist s) := by unfold ParentsExist; infer_instance
set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (ParentLt s) := by unfold ParentLt; infer_instance
set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (ParentCoversActive s) := by
  unfold ParentCoversActive; infer_instance
set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (ExclChildLoaned s) := by unfold ExclChildLoaned; infer_instance
set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (SharedChildBelowOwn s) := by
  unfold SharedChildBelowOwn; infer_instance
set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (SharedChildrenShared s) := by
  unfold SharedChildrenShared; infer_instance
set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (DepthCounts s) := by unfold DepthCounts; infer_instance
set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (RootsDisjoint s) := by unfold RootsDisjoint; infer_instance

/-- The loan-tree invariant: all seven structural laws. -/
structure LoanTreeInv (s : State) : Prop where
  parentLt : ParentLt s
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
  rootsDisjoint : RootsDisjoint s

instance (s : State) : Decidable (LoanTreeInv s) :=
  decidable_of_iff (ParentLt s ∧ ParentCoversActive s ∧ ExclChildLoaned s ∧
      SharedChildBelowOwn s ∧ SharedChildrenShared s ∧ DepthCounts s ∧ RootsDisjoint s)
    ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
     fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

/-- The five *tree-local* laws: the laws that relate a view only to its parent and its direct
children (`ParentCoversActive`, `ExclChildLoaned`, `SharedChildBelowOwn`, `SharedChildrenShared`,
`DepthCounts`). The remaining two laws of `LoanTreeInv` are global: `ParentLt` (well-founded parent
links) and `RootsDisjoint` (one active root per cell). Ending a view never touches parent links,
domains or roots, so the two global laws are preserved by every raw end
(`endRaw_preserves_parentLt`, `endRaw_preserves_rootsDisjoint`); the five local laws are the ones
whose preservation needs return authority. -/
structure LocalLoanLaws (s : State) : Prop where
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s

instance (s : State) : Decidable (LocalLoanLaws s) :=
  decidable_of_iff (ParentCoversActive s ∧ ExclChildLoaned s ∧ SharedChildBelowOwn s ∧
      SharedChildrenShared s ∧ DepthCounts s)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- `LoanTreeInv` is exactly the five local laws plus the two global ones. -/
theorem loanTreeInv_iff_local (s : State) :
    LoanTreeInv s ↔ (ParentLt s ∧ LocalLoanLaws s ∧ RootsDisjoint s) :=
  ⟨fun h => ⟨h.parentLt, ⟨h.parentCoversActive, h.exclChildLoaned, h.sharedChildBelowOwn,
      h.sharedChildrenShared, h.depthCounts⟩, h.rootsDisjoint⟩,
   fun ⟨h1, h2, h3⟩ => ⟨h1, h2.parentCoversActive, h2.exclChildLoaned, h2.sharedChildBelowOwn,
      h2.sharedChildrenShared, h2.depthCounts, h3⟩⟩

/-! ## The safety property (state part) -/

/-- Write exclusivity: a view that can write a cell is the only active view that can access it
(no two writers, and no reader beside a writer). -/
def WriteExclusive (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.canWrite v a = true → s.canRead w a = false

set_option synthInstance.maxSize 4096 in
instance (s : State) : Decidable (WriteExclusive s) := by unfold WriteExclusive; infer_instance

theorem writeExclusive_iff_unbounded (s : State) :
    WriteExclusive s ↔ ∀ v w a, v ≠ w → s.canWrite v a = true → s.canRead w a = false := by
  constructor
  · intro h v w a hne hw
    cases hr : s.canRead w a with
    | false => rfl
    | true =>
      have hv : v < s.size := State.isActive_lt_size (by
        unfold State.canWrite at hw; simp only [Bool.and_eq_true] at hw; exact hw.1)
      have hw' : w < s.size := State.isActive_lt_size (by
        unfold State.canRead at hr; simp only [Bool.and_eq_true] at hr; exact hr.1)
      have ha : a < s.width := State.covers_lt_width (v := v) (by
        unfold State.canWrite at hw; simp only [Bool.and_eq_true, beq_iff_eq] at hw
        unfold State.covers; unfold State.depth? at hw
        cases hc : s.cell? v a with
        | none => simp [hc] at hw
        | some _ => rfl)
      have := h v hv w hw' a ha hne hw
      rw [hr] at this; exact this
  · intro h v _ w _ a _ hne hw
    exact h v w a hne hw

/-- Access requires activity (the first clause of the safety property holds by construction). -/
theorem read_isSome_imp_isActive {s : State} {v : ViewId} {a : Addr} (h : (read s v a).isSome) :
    s.isActive v = true := by
  unfold read State.canRead at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true] at hc; exact hc.1
  · simp at h

theorem write_isSome_imp_isActive {s : State} {v : ViewId} {a : Addr} {b : Byte}
    (h : (write s v a b).isSome) : s.isActive v = true := by
  unfold write at h
  split at h
  · simp at h
  · split at h
    · rename_i hc; unfold State.canWrite at hc; simp only [Bool.and_eq_true] at hc; exact hc.1
    · simp at h

end Toy.Views
