import ToySendSync.Place

/-!
# Characterizations of `SemSend` and `SemSync` per type constructor
-/

namespace Toy.SendSync

/-! ## Plain data -/

theorem semSend_plain : SemSend .plain :=
  ⟨race_nil_right _, nfr_of_no_rel (by decide)⟩

theorem semSync_plain : SemSync .plain :=
  ⟨not_race_of_no_conflict (by decide), nfr_of_no_rel (by decide)⟩

/-! ## Cell and RefCell -/

theorem semSend_cell_iff (U : Ty) : SemSend (.cell U) ↔ SemSend U := by
  simp only [SemSend, fp, race_append_left, nfr_append, nfr_place_nil, race_place_nil_nil,
    not_race_root_place loc_cellRoot, false_or, nfr_cellRoot, true_and]

theorem not_semSync_cell (U : Ty) : ¬ SemSync (.cell U) := by
  intro h
  apply h.1
  refine ⟨rootEv .wr, by simp [fp], rootEv .wr, by simp [fp], by decide, compatible_nil_nil⟩

theorem semSend_refCell_iff (U : Ty) : SemSend (.refCell U) ↔ SemSend U := by
  simp only [SemSend, fp, race_append_left, nfr_append, nfr_place_nil, nfr_place_fresh,
    race_place_nil_nil, race_place_fresh_nil, not_race_root_place loc_cellRoot, false_or,
    nfr_cellRoot, true_and]
  constructor
  · rintro ⟨hr, hn, _, _⟩
    exact ⟨fun h => hr (Or.inl h), hn⟩
  · rintro ⟨hr, hn⟩
    refine ⟨?_, hn, nfr_shr_of_own _ U hn, hn⟩
    rintro (h | h | h)
    · exact hr h
    · exact hr (race_mono (shr_subset_own U) (fun _ h => h) h)
    · exact hr h

theorem not_semSync_refCell (U : Ty) : ¬ SemSync (.refCell U) := by
  intro h
  apply h.1
  refine ⟨rootEv .wr, by simp [fp], rootEv .wr, by simp [fp], by decide, compatible_nil_nil⟩

/-! ## Rc -/

theorem not_semSend_rc (U : Ty) : ¬ SemSend (.rc U) := by
  intro h
  apply h.1
  refine ⟨rootEv .wr [.via []], by simp [fp], rootEv .wr [.via []], by simp [fp], by decide,
    compatible_via_via []⟩

theorem not_semSync_rc (U : Ty) : ¬ SemSync (.rc U) := by
  intro h
  apply h.1
  refine ⟨rootEv .wr [.via []], by simp [fp], rootEv .wr [.via []], by simp [fp], by decide,
    compatible_via_via []⟩

/-! ## Arc -/

theorem arc_race_iff (U : Ty) :
    Race (fp (.arc U)).own ((fp (.arc U)).own ++ place [] 0 (fp U).alias) ↔
      Race (fp U).shr (fp U).shr ∨ Race (fp U).shr (fp U).alias ∨ Race (fp U).own (fp U).alias := by
  simp only [fp, race_append_left, race_append_right, race_place_via_via,
    race_place_via_nil, race_place_uniq_nil, not_race_place_via_uniq, not_race_place_uniq_via,
    not_race_place_uniq_uniq, not_race_root_place loc_arcRoot, not_race_place_root loc_arcRoot,
    not_race_arcRoot_arcRoot, false_or, or_false]

theorem semSend_arc_iff (U : Ty) : SemSend (.arc U) ↔ SemSend U ∧ SemSync U := by
  have hown : (fp (.arc U)).own = (fp (.arc U)).own := rfl
  have halias : (fp (.arc U)).alias = (fp (.arc U)).own ++ place [] 0 (fp U).alias := rfl
  unfold SemSend
  rw [halias, arc_race_iff]
  simp only [SemSync, race_append_right]
  have hnfr : NoForeignRelease .other (fp (.arc U)).own ↔ NoForeignRelease .other (fp U).own := by
    simp only [fp, nfr_append, nfr_place_via, nfr_place_uniq, nfr_arcRoot, true_and]
    exact ⟨fun h => h.2, fun h => ⟨nfr_shr_of_own _ U h, h⟩⟩
  rw [hnfr]
  constructor
  · rintro ⟨hr, hn⟩
    refine ⟨⟨fun h => hr (Or.inr (Or.inr h)), hn⟩, ?_, nfr_shr_of_own _ U hn⟩
    rintro (h | h)
    · exact hr (Or.inl h)
    · exact hr (Or.inr (Or.inl h))
  · rintro ⟨⟨hr₁, hn⟩, hr₂, _⟩
    refine ⟨?_, hn⟩
    rintro (h | h | h)
    · exact hr₂ (Or.inl h)
    · exact hr₂ (Or.inr h)
    · exact hr₁ h

theorem semSync_arc_iff (U : Ty) : SemSync (.arc U) ↔ SemSend U ∧ SemSync U := by
  have h : SemSync (.arc U) ↔ SemSend (.arc U) := by
    unfold SemSync SemSend
    have hs : (fp (.arc U)).shr = (fp (.arc U)).own := rfl
    have ha : (fp (.arc U)).alias = (fp (.arc U)).own ++ place [] 0 (fp U).alias := rfl
    rw [hs, ha, race_append_right (fp (.arc U)).own (fp (.arc U)).own, race_append_right]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun h => h₁ (by rcases h with h | h <;> simp [h]), h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun h => h₁ (by rcases h with h | h | h <;> simp [h]), h₂⟩
  rw [h, semSend_arc_iff]

/-! ## Mutex -/

theorem semSend_mutex_iff (U : Ty) : SemSend (.mutex U) ↔ SemSend U := by
  simp only [SemSend, fp, race_append_left, nfr_append, nfr_place_nil, nfr_place_fresh,
    race_place_nil_nil, race_place_fresh_nil, not_race_root_place loc_mutexRoot, nfr_mutexRoot,
    or_false, or_self, and_true, and_self]

theorem semSync_mutex_iff (U : Ty) : SemSync (.mutex U) ↔ SemSend U := by
  simp only [SemSync, SemSend, fp, race_append_left, race_append_right, nfr_append,
    nfr_place_fresh, nfr_mutexRoot, race_place_fresh_nil, not_race_place_fresh_fresh,
    not_race_place_root loc_mutexRoot, not_race_root_place loc_mutexRoot,
    not_race_mutexRoot_mutexRoot, false_or, or_false, and_true]

/-! ## MutexGuard -/

theorem not_semSend_guard (U : Ty) : ¬ SemSend (.guard U) := by
  intro h
  have := h.2
  simp only [fp, nfr_append] at this
  exact not_nfr_guardRoot this.2

theorem semSync_guard_iff (U : Ty) : SemSync (.guard U) ↔ SemSync U := by
  simp only [SemSync, fp, race_append_right, nfr_place_guard, race_place_guard_guard,
    race_place_guard_nil, not_race_place_guard_fresh, false_or]

/-! ## Structural constructors -/

theorem semSend_box_iff (U : Ty) : SemSend (.box U) ↔ SemSend U := Iff.rfl

theorem semSync_box_iff (U : Ty) : SemSync (.box U) ↔ SemSync U := Iff.rfl

theorem semSend_refMut_iff (U : Ty) : SemSend (.refMut U) ↔ SemSend U := Iff.rfl

theorem semSync_refMut_iff (U : Ty) : SemSync (.refMut U) ↔ SemSync U := Iff.rfl

theorem semSync_ref_iff (U : Ty) : SemSync (.ref U) ↔ SemSync U := by
  unfold SemSync
  show (¬ Race (fp U).shr ((fp U).shr ++ ((fp U).shr ++ (fp U).alias)) ∧ _) ↔ _
  rw [race_append_right (fp U).shr (fp U).shr ((fp U).shr ++ (fp U).alias),
    race_append_right (fp U).shr (fp U).shr (fp U).alias]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun h => h₁ (by rcases h with h | h <;> simp [h]), h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun h => h₁ (by rcases h with h | h | h <;> simp [h]), h₂⟩

theorem semSend_prod_iff (A B : Ty) : SemSend (.prod A B) ↔ SemSend A ∧ SemSend B := by
  simp only [SemSend, fp, race_append_left, race_append_right, nfr_append, nfr_place_nil,
    race_place_nil_nil, not_race_place_01, not_race_place_10, or_false, false_or, not_or]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨⟨h₁, h₃⟩, h₂, h₄⟩
  · rintro ⟨⟨h₁, h₃⟩, h₂, h₄⟩
    exact ⟨⟨h₁, h₂⟩, h₃, h₄⟩

theorem semSync_prod_iff (A B : Ty) : SemSync (.prod A B) ↔ SemSync A ∧ SemSync B := by
  simp only [SemSync, fp, race_append_left, race_append_right, nfr_append, nfr_place_nil,
    race_place_nil_nil, not_race_place_01, not_race_place_10, or_false, false_or, not_or]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩
    exact ⟨⟨⟨h₁, h₃⟩, h₅⟩, ⟨h₂, h₄⟩, h₆⟩
  · rintro ⟨⟨⟨h₁, h₃⟩, h₅⟩, ⟨h₂, h₄⟩, h₆⟩
    exact ⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩

theorem semSend_sum_iff (A B : Ty) : SemSend (.sum A B) ↔ SemSend A ∧ SemSend B :=
  semSend_prod_iff A B

theorem semSync_sum_iff (A B : Ty) : SemSync (.sum A B) ↔ SemSync A ∧ SemSync B :=
  semSync_prod_iff A B

theorem semSend_wrap_iff (f : Ty) (v : View) (u : Bool) : SemSend (.wrap f v u) ↔ SemSend f :=
  Iff.rfl

theorem semSync_wrap_of_semSync (f : Ty) (v : View) (u : Bool) :
    SemSync f → SemSync (.wrap f v u) := by
  rintro ⟨h₁, h₂⟩
  refine ⟨fun h => h₁ (race_mono (expose_subset v _) ?_ h), nfr_mono (expose_subset v _) h₂⟩
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact List.mem_append.mpr (Or.inl (expose_subset v _ e h))
  · exact List.mem_append.mpr (Or.inr h)

theorem semSync_wrap_full_iff (f : Ty) (u : Bool) : SemSync (.wrap f .full u) ↔ SemSync f :=
  Iff.rfl

theorem semSync_wrap_none (f : Ty) (u : Bool) : SemSync (.wrap f .none u) :=
  ⟨race_nil_left _, nfr_nil _⟩

end Toy.SendSync
