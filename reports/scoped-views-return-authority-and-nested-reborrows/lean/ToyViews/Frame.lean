import ToyViews.Naive

/-!
# Frame lemmas for the operations

Structural facts about `setView`, `mapCells`, `restoreCells` and the operations `borrow`, `share`,
`write`, `endRaw`: which view metadata (count, parent links, activity, modes, covered domains) each
operation changes. In particular, a raw end never changes the number of views, any parent link, any
mode, or any covered domain, and it changes activity only by retiring the ended view; hence it
preserves the two global laws `ParentLt` and `RootsDisjoint` unconditionally.
-/

namespace Toy.Views

theorem setView_size (s : State) (v : ViewId) (vw : View) :
    (s.setView v vw).size = s.size := by
  unfold State.setView State.size
  exact List.length_set

theorem view?_setView (s : State) (p v : ViewId) (vw : View) (hp : p < s.size) :
    (s.setView p vw).view? v = if v = p then some vw else s.view? v := by
  unfold State.setView State.view?
  unfold State.size at hp
  rw [List.getElem?_set]
  by_cases h : v = p
  · subst h; simp [hp]
  · have hne : p ≠ v := fun e => h e.symm
    simp [h, hne]

theorem cell?_mapCells (vw : View) (n : Nat) (f : Addr → Option Cell → Option Cell) (a : Addr) :
    (vw.mapCells n f).cell? a = if a < n then f a (vw.cell? a) else none := by
  unfold View.mapCells View.cell?
  rcases Nat.lt_or_ge a n with ha | ha
  · simp [ha, List.getD_eq_getElem?_getD]
  · have hnot : ¬ a < n := Nat.not_lt.mpr ha
    simp only [hnot, ↓reduceIte, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp [ha])]
    rfl

theorem cell?_eq_none_of_ge {vw : View} {a : Addr} (ha : vw.cells.length ≤ a) :
    vw.cell? a = none := by
  unfold View.cell?
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha]
  rfl

theorem lt_length_of_cell?_isSome {vw : View} {a : Addr} (h : (vw.cell? a).isSome = true) :
    a < vw.cells.length := by
  rcases Nat.lt_or_ge a vw.cells.length with ha | ha
  · exact ha
  · rw [cell?_eq_none_of_ge ha] at h; simp at h

theorem mem_domain_iff {vw : View} {a : Addr} :
    a ∈ vw.domain ↔ (vw.cell? a).isSome = true := by
  unfold View.domain
  simp only [List.mem_filter, List.mem_range]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨lt_length_of_cell?_isSome h, h⟩⟩


/-- What `returnable` guarantees at each covered address of the child: an exclusive child's cell
is recorded in the parent as `loaned c`; a shared child's cell is an `own` cell of the parent at a
positive depth strictly above the parent's own baseline. Also, the parent is active. -/
theorem returnable_spec {vc vp : View} {c : ViewId} (h : returnable vc vp c = true)
    {a : Addr} (hc : (vc.cell? a).isSome = true) :
    (vc.mode = .excl ∧ vp.cell? a = some (.loaned c)) ∨
    (vc.mode = .shared ∧ ∃ d b, vp.cell? a = some (.own (d + 1) b) ∧ vp.mode.baseline < d + 1) := by
  have ha : a < vc.cells.length := lt_length_of_cell?_isSome hc
  unfold returnable at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have ha' := h.2 a (List.mem_range.mpr ha)
  cases hca : vc.cell? a with
  | none => rw [hca] at hc; simp at hc
  | some _ =>
    simp only [hca] at ha'
    cases hm : vc.mode with
    | excl =>
      simp only [hm] at ha'
      cases hpa : vp.cell? a with
      | none => simp [hpa] at ha'
      | some pcell =>
        cases pcell with
        | own _ _ => simp [hpa] at ha'
        | loaned c' =>
          simp only [hpa, beq_iff_eq] at ha'
          subst ha'
          exact Or.inl ⟨rfl, rfl⟩
    | shared =>
      simp only [hm] at ha'
      cases hpa : vp.cell? a with
      | none => simp [hpa] at ha'
      | some pcell =>
        cases pcell with
        | loaned _ => simp [hpa] at ha'
        | own d b =>
          simp only [hpa, decide_eq_true_eq] at ha'
          cases d with
          | zero => exact absurd ha' (Nat.not_lt_zero _)
          | succ d' => exact Or.inr ⟨rfl, d', b, rfl, ha'⟩

/-- `returnable` requires the parent to be active. -/
theorem returnable_parent_active {vc vp : View} {c : ViewId} (h : returnable vc vp c = true) :
    vp.active = true := by
  unfold returnable at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem restoreCells_isSome_eq {vc vp : View} {c : ViewId} (r : Addr → Byte)
    (hret : returnable vc vp c = true) (a : Addr) :
    ((restoreCells vc vp r).cell? a).isSome = (vp.cell? a).isSome := by
  unfold restoreCells
  rw [cell?_mapCells]
  rcases Nat.lt_or_ge a (max vp.cells.length vc.cells.length) with ha | ha
  · simp only [ha, ↓reduceIte]
    cases hca : vc.cell? a with
    | none => rfl
    | some _ =>
      have hc : (vc.cell? a).isSome = true := by simp [hca]
      rcases returnable_spec hret hc with ⟨hm, hpa⟩ | ⟨hm, d, b, hpa, -⟩
      · simp [hm, hpa]
      · simp [hm, hpa]
  · have hnot : ¬ a < max vp.cells.length vc.cells.length := Nat.not_lt.mpr ha
    simp only [hnot, ↓reduceIte]
    have hpge : vp.cells.length ≤ a := Nat.le_trans (Nat.le_max_left _ _) ha
    rw [cell?_eq_none_of_ge hpge]

theorem restoreCells_domain {vc vp : View} {c : ViewId} (r : Addr → Byte)
    (hret : returnable vc vp c = true) :
    (restoreCells vc vp r).domain = vp.domain := by
  have hfilter : ∀ m,
      (List.range m).filter (fun a => ((restoreCells vc vp r).cell? a).isSome) =
      (List.range m).filter (fun a => (vp.cell? a).isSome) := by
    intro m
    congr 1; funext a
    exact restoreCells_isSome_eq r hret a
  have hdrop : ∀ (vw : View) (m : Nat), vw.cells.length ≤ m →
      (List.range m).filter (fun a => (vw.cell? a).isSome) = vw.domain := by
    intro vw m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = vw.cells.length + k := ⟨m - vw.cells.length, by omega⟩
    induction k with
    | zero => simp [View.domain]
    | succ k ih =>
      rw [Nat.add_succ, List.range_succ, List.filter_append]
      have hnone : (vw.cell? (vw.cells.length + k)).isSome = false := by
        rw [cell?_eq_none_of_ge (by omega)]; rfl
      simp [hnone, ih (by omega)]
  let M := max vp.cells.length (restoreCells vc vp r).cells.length
  rw [← hdrop (restoreCells vc vp r) M (Nat.le_max_right _ _),
      ← hdrop vp M (Nat.le_max_left _ _)]
  exact hfilter M

theorem endRaw_unpack {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hend : endRaw s c r = some s') :
    ∃ vc p vp vc₁,
      s.view? c = some vc ∧ vc.parent = some p ∧ s.view? p = some vp ∧
      vc.active = true ∧ returnable vc vp c = true ∧
      (s.setView p (restoreCells vc vp r)).view? c = some vc₁ ∧
      s' = (s.setView p (restoreCells vc vp r)).setView c { vc₁ with active := false } := by
  unfold endRaw at hend
  cases hvc : s.view? c with
  | none => rw [hvc] at hend; simp at hend
  | some vc =>
    rw [hvc] at hend; dsimp only at hend
    cases hp : vc.parent with
    | none => rw [hp] at hend; simp at hend
    | some p =>
      rw [hp] at hend; dsimp only at hend
      cases hvp : s.view? p with
      | none => rw [hvp] at hend; simp at hend
      | some vp =>
        rw [hvp] at hend; dsimp only at hend
        by_cases hcond : (vc.active && returnable vc vp c) = true
        · simp only [hcond, ↓reduceIte] at hend
          cases hvc1 : (s.setView p (restoreCells vc vp r)).view? c with
          | none => rw [hvc1] at hend; simp at hend
          | some vc₁ =>
            rw [hvc1] at hend; simp only [Option.some.injEq] at hend
            simp only [Bool.and_eq_true] at hcond
            exact ⟨vc, p, vp, vc₁, rfl, hp, hvp, hcond.1, hcond.2, hvc1, hend.symm⟩
        · simp [hcond] at hend

theorem endRaw_size {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hend : endRaw s c r = some s') : s'.size = s.size := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := endRaw_unpack hend
  rw [setView_size, setView_size]

theorem endRaw_parentOf {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hend : endRaw s c r = some s') (v : ViewId) :
    s'.parentOf v = s.parentOf v := by
  obtain ⟨vc, p, vp, vc₁, hvc, _, hvp, _, _, hvc1, rfl⟩ := endRaw_unpack hend
  have hc : c < s.size := State.lt_size_of_view?_eq_some hvc
  have hp : p < s.size := State.lt_size_of_view?_eq_some hvp
  have hc1 : c < (s.setView p (restoreCells vc vp r)).size := by rw [setView_size]; exact hc
  unfold State.parentOf
  rw [view?_setView _ c v _ hc1]
  by_cases hvc_eq : v = c
  · subst hvc_eq
    simp only [↓reduceIte, Option.bind_some]
    rw [view?_setView _ p v _ hp] at hvc1
    by_cases hcp : v = p
    · subst hcp
      simp only [↓reduceIte, Option.some.injEq] at hvc1
      subst hvc1
      rw [hvp]; rfl
    · simp only [hcp, ↓reduceIte] at hvc1
      rw [hvc] at hvc1
      simp only [Option.some.injEq] at hvc1
      subst hvc1
      rw [hvc]; rfl
  · simp only [hvc_eq, ↓reduceIte]
    rw [view?_setView _ p v _ hp]
    by_cases hvp_eq : v = p
    · subst hvp_eq
      simp only [↓reduceIte]
      rw [hvp]; rfl
    · simp [hvp_eq]

theorem endRaw_covers {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hend : endRaw s c r = some s') (v : ViewId) (a : Addr) :
    s'.covers v a = s.covers v a := by
  obtain ⟨vc, p, vp, vc₁, hvc, _, hvp, _, hret, hvc1, rfl⟩ := endRaw_unpack hend
  have hc : c < s.size := State.lt_size_of_view?_eq_some hvc
  have hp : p < s.size := State.lt_size_of_view?_eq_some hvp
  have hc1 : c < (s.setView p (restoreCells vc vp r)).size := by rw [setView_size]; exact hc
  unfold State.covers State.cell?
  rw [view?_setView _ c v _ hc1]
  by_cases hvc_eq : v = c
  · subst hvc_eq
    simp only [↓reduceIte, Option.bind_some]
    rw [view?_setView _ p v _ hp] at hvc1
    by_cases hcp : v = p
    · subst hcp
      simp only [↓reduceIte, Option.some.injEq] at hvc1
      subst hvc1
      rw [hvp]
      simp only [Option.bind_some]
      exact restoreCells_isSome_eq r hret a
    · simp only [hcp, ↓reduceIte] at hvc1
      rw [hvc] at hvc1
      simp only [Option.some.injEq] at hvc1
      subst hvc1
      rw [hvc]; rfl
  · simp only [hvc_eq, ↓reduceIte]
    rw [view?_setView _ p v _ hp]
    by_cases hvp_eq : v = p
    · subst hvp_eq
      simp only [↓reduceIte, Option.bind_some]
      rw [hvp]
      simp only [Option.bind_some]
      exact restoreCells_isSome_eq r hret a
    · simp [hvp_eq]

theorem endRaw_isActive {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hend : endRaw s c r = some s') (v : ViewId) :
    s'.isActive v = (if v = c then false else s.isActive v) := by
  obtain ⟨vc, p, vp, vc₁, hvc, _, hvp, _, _, _, rfl⟩ := endRaw_unpack hend
  have hc : c < s.size := State.lt_size_of_view?_eq_some hvc
  have hp : p < s.size := State.lt_size_of_view?_eq_some hvp
  have hc1 : c < (s.setView p (restoreCells vc vp r)).size := by rw [setView_size]; exact hc
  unfold State.isActive
  rw [view?_setView _ c v _ hc1]
  by_cases hvc_eq : v = c
  · subst hvc_eq; simp
  · simp only [hvc_eq, ↓reduceIte]
    rw [view?_setView _ p v _ hp]
    by_cases hvp_eq : v = p
    · subst hvp_eq; simp [hvp]; rfl
    · simp [hvp_eq]

theorem endRaw_modeOf {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hend : endRaw s c r = some s') (v : ViewId) :
    s'.modeOf v = s.modeOf v := by
  obtain ⟨vc, p, vp, vc₁, hvc, _, hvp, _, _, hvc1, rfl⟩ := endRaw_unpack hend
  have hc : c < s.size := State.lt_size_of_view?_eq_some hvc
  have hp : p < s.size := State.lt_size_of_view?_eq_some hvp
  have hc1 : c < (s.setView p (restoreCells vc vp r)).size := by rw [setView_size]; exact hc
  unfold State.modeOf
  rw [view?_setView _ c v _ hc1]
  by_cases hvc_eq : v = c
  · subst hvc_eq
    simp only [↓reduceIte, Option.map_some]
    rw [view?_setView _ p v _ hp] at hvc1
    by_cases hcp : v = p
    · subst hcp
      simp only [↓reduceIte, Option.some.injEq] at hvc1
      subst hvc1; rw [hvp]; rfl
    · simp only [hcp, ↓reduceIte] at hvc1
      rw [hvc] at hvc1; simp only [Option.some.injEq] at hvc1
      subst hvc1; rw [hvc]; rfl
  · simp only [hvc_eq, ↓reduceIte]
    rw [view?_setView _ p v _ hp]
    by_cases hvp_eq : v = p
    · subst hvp_eq; simp [hvp]; rfl
    · simp [hvp_eq]

theorem endRaw_baselineOf {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hend : endRaw s c r = some s') (v : ViewId) :
    s'.baselineOf v = s.baselineOf v := by
  unfold State.baselineOf
  rw [endRaw_modeOf hend v]


/-- `endRaw` preserves `ParentLt` unconditionally — without `ReturnAuthority` and without
any of the other six structural laws. -/
theorem endRaw_preserves_parentLt {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hlt : ParentLt s) (hend : endRaw s c r = some s') : ParentLt s' := by
  intro v hv p hp
  rw [endRaw_size hend] at hv
  rw [endRaw_parentOf hend v] at hp
  exact hlt v hv p hp

/-- `endRaw` preserves `RootsDisjoint` unconditionally — without `ReturnAuthority` and
without any of the other six structural laws. -/
theorem endRaw_preserves_rootsDisjoint {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hrd : RootsDisjoint s) (hend : endRaw s c r = some s') : RootsDisjoint s' := by
  intro v hv w hw a _ hne hactv hactw hpv hpw hcovv
  rw [endRaw_size hend] at hv hw
  rw [endRaw_parentOf hend v] at hpv
  rw [endRaw_parentOf hend w] at hpw
  rw [endRaw_covers hend v a] at hcovv
  rw [endRaw_covers hend w a]
  rw [endRaw_isActive hend v] at hactv
  rw [endRaw_isActive hend w] at hactw
  have hvc : v ≠ c := by intro e; subst e; simp at hactv
  have hwc : w ≠ c := by intro e; subst e; simp at hactw
  simp only [hvc, ↓reduceIte] at hactv
  simp only [hwc, ↓reduceIte] at hactw
  exact hrd v hv w hw a (State.covers_lt_width hcovv) hne hactv hactw hpv hpw hcovv

/-! ## View counts of the operations -/

theorem borrow_size {s s₁ : State} {p : ViewId} {A : List Addr} (hb : borrow s p A = some s₁) :
    s₁.size = s.size + 1 := by
  unfold borrow at hb
  cases hvp : s.view? p with
  | none => rw [hvp] at hb; simp at hb
  | some vp =>
    rw [hvp] at hb; dsimp only at hb
    split at hb
    · simp only [Option.some.injEq] at hb; subst hb; simp [State.size]
    · simp at hb

theorem share_size {s s₁ : State} {p : ViewId} {A : List Addr} (hb : share s p A = some s₁) :
    s₁.size = s.size + 1 := by
  unfold share at hb
  cases hvp : s.view? p with
  | none => rw [hvp] at hb; simp at hb
  | some vp =>
    rw [hvp] at hb; dsimp only at hb
    split at hb
    · simp only [Option.some.injEq] at hb; subst hb; simp [State.size]
    · simp at hb

theorem write_size {s s' : State} {v : ViewId} {a : Addr} {b : Byte}
    (hw : write s v a b = some s') : s'.size = s.size := by
  unfold write at hw
  cases hvw : s.view? v with
  | none => rw [hvw] at hw; simp at hw
  | some vw =>
    rw [hvw] at hw; dsimp only at hw
    split at hw
    · simp only [Option.some.injEq] at hw; subst hw; exact setView_size _ _ _
    · simp at hw

end Toy.Views
