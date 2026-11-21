import ToySendSync.Lemmas

/-!
# Specialized race lemmas for the root claims used by `fp`
-/

namespace Toy.SendSync

theorem race_place_nil_nil (i : Nat) (B A : List Ev) :
    Race (place [] i B) (place [] i A) ↔ Race B A := by
  rw [race_place [] [] i i B A (by decide) (by decide)]
  simp [compatible_nil_nil]

theorem race_place_single_nil (c : Claim) (hc : c.path = []) (i : Nat) (B A : List Ev) :
    Race (place [c] i B) (place [] i A) ↔ Race B A := by
  rw [race_place [c] [] i i B A (by simpa using hc) (by decide)]
  simp [compatible_single_nil]

theorem race_place_via_nil (i : Nat) (B A : List Ev) :
    Race (place [.via []] i B) (place [] i A) ↔ Race B A :=
  race_place_single_nil _ rfl i B A

theorem race_place_uniq_nil (i : Nat) (B A : List Ev) :
    Race (place [.uniq []] i B) (place [] i A) ↔ Race B A :=
  race_place_single_nil _ rfl i B A

theorem race_place_fresh_nil (i : Nat) (B A : List Ev) :
    Race (place [.held [] .fresh] i B) (place [] i A) ↔ Race B A :=
  race_place_single_nil _ rfl i B A

theorem race_place_guard_nil (i : Nat) (B A : List Ev) :
    Race (place [.held [] (.guard [])] i B) (place [] i A) ↔ Race B A :=
  race_place_single_nil _ rfl i B A

theorem race_place_via_via (i : Nat) (B A : List Ev) :
    Race (place [.via []] i B) (place [.via []] i A) ↔ Race B A := by
  rw [race_place _ _ i i B A (by decide) (by decide)]
  simp [compatible_via_via]

theorem race_place_guard_guard (i : Nat) (B A : List Ev) :
    Race (place [.held [] (.guard [])] i B) (place [.held [] (.guard [])] i A) ↔ Race B A := by
  rw [race_place _ _ i i B A (by decide) (by decide)]
  simp [compatible_guard_guard]

theorem not_race_place_via_uniq (i : Nat) (B A : List Ev) :
    ¬ Race (place [.via []] i B) (place [.uniq []] i A) := by
  rw [race_place _ _ i i B A (by decide) (by decide)]
  simp [not_compatible_via_uniq]

theorem not_race_place_uniq_via (i : Nat) (B A : List Ev) :
    ¬ Race (place [.uniq []] i B) (place [.via []] i A) := by
  rw [race_place _ _ i i B A (by decide) (by decide)]
  simp [not_compatible_uniq_via]

theorem not_race_place_uniq_uniq (i : Nat) (B A : List Ev) :
    ¬ Race (place [.uniq []] i B) (place [.uniq []] i A) := by
  rw [race_place _ _ i i B A (by decide) (by decide)]
  simp [not_compatible_uniq_uniq]

theorem not_race_place_fresh_fresh (i : Nat) (B A : List Ev) :
    ¬ Race (place [.held [] .fresh] i B) (place [.held [] .fresh] i A) := by
  rw [race_place _ _ i i B A (by decide) (by decide)]
  simp [not_compatible_fresh_fresh]

theorem not_race_place_guard_fresh (i : Nat) (B A : List Ev) :
    ¬ Race (place [.held [] (.guard [])] i B) (place [.held [] .fresh] i A) := by
  rw [race_place _ _ i i B A (by decide) (by decide)]
  simp [not_compatible_guard_fresh]

theorem not_race_place_ne {i j : Nat} (hij : i ≠ j) (r₁ r₂ : List Claim) (B A : List Ev) :
    ¬ Race (place r₁ i B) (place r₂ j A) := by
  rintro ⟨e₁, h₁, e₂, h₂, hc, _⟩
  obtain ⟨e₁', _, rfl⟩ := List.mem_map.mp h₁
  obtain ⟨e₂', _, rfl⟩ := List.mem_map.mp h₂
  exact hij ((conflicting_place r₁ r₂ i j e₁' e₂').mp hc).1

theorem not_race_place_01 (r₁ r₂ : List Claim) (B A : List Ev) :
    ¬ Race (place r₁ 0 B) (place r₂ 1 A) := not_race_place_ne (by decide) r₁ r₂ B A

theorem not_race_place_10 (r₁ r₂ : List Claim) (B A : List Ev) :
    ¬ Race (place r₁ 1 B) (place r₂ 0 A) := not_race_place_ne (by decide) r₁ r₂ B A

/-! Release affinity under the root claims used by `fp`. -/

theorem nfr_place_nil (t : Tid) (i : Nat) (L : List Ev) :
    NoForeignRelease t (place [] i L) ↔ NoForeignRelease t L :=
  nfr_place t [] (by decide) i L

theorem nfr_place_fresh (t : Tid) (i : Nat) (L : List Ev) :
    NoForeignRelease t (place [.held [] .fresh] i L) ↔ NoForeignRelease t L :=
  nfr_place t _ (by decide) i L

theorem nfr_place_guard (t : Tid) (i : Nat) (L : List Ev) :
    NoForeignRelease t (place [.held [] (.guard [])] i L) ↔ NoForeignRelease t L :=
  nfr_place t _ (by decide) i L

theorem nfr_place_via (t : Tid) (i : Nat) (L : List Ev) :
    NoForeignRelease t (place [.via []] i L) ↔ NoForeignRelease t L :=
  nfr_place t _ (by decide) i L

theorem nfr_place_uniq (t : Tid) (i : Nat) (L : List Ev) :
    NoForeignRelease t (place [.uniq []] i L) ↔ NoForeignRelease t L :=
  nfr_place t _ (by decide) i L

/-! Root event lists used by `fp`. -/

theorem loc_cellRoot : ∀ e ∈ [rootEv .rd, rootEv .wr], e.loc = [] := by decide

theorem loc_arcRoot : ∀ e ∈ [rootEv .atomic [.via []]], e.loc = [] := by decide

theorem loc_mutexRoot : ∀ e ∈ [rootEv .rel [.held [] .fresh]], e.loc = [] := by decide

theorem loc_guardRoot : ∀ e ∈ [rootEv .rel [.held [] (.guard [])]], e.loc = [] := by decide

theorem nfr_cellRoot (t : Tid) : NoForeignRelease t [rootEv .rd, rootEv .wr] :=
  nfr_of_no_rel (by decide)

theorem nfr_arcRoot (t : Tid) : NoForeignRelease t [rootEv .atomic [.via []]] :=
  nfr_of_no_rel (by decide)

/-- A release of a `fresh` acquisition is made by the thread that acquired it. -/
theorem nfr_mutexRoot (t : Tid) : NoForeignRelease t [rootEv .rel [.held [] .fresh]] := by
  intro e he a _ hm
  rw [List.mem_singleton.mp he] at hm
  simp only [rootEv, List.mem_singleton, Claim.held.injEq, true_and] at hm
  subst hm
  rfl

/-- The other thread releasing a guard's acquisition is a foreign release. -/
theorem not_nfr_guardRoot : ¬ NoForeignRelease .other [rootEv .rel [.held [] (.guard [])]] := by
  intro h
  have := h _ (List.mem_singleton.mpr rfl) (.guard []) rfl (List.mem_singleton.mpr rfl)
  cases this

theorem not_race_mutexRoot_mutexRoot :
    ¬ Race [rootEv .rel [.held [] .fresh]] [rootEv .rel [.held [] .fresh]] :=
  not_race_of_no_conflict (by decide)

theorem not_race_arcRoot_arcRoot :
    ¬ Race [rootEv .atomic [.via []]] [rootEv .atomic [.via []]] :=
  not_race_of_no_conflict (by decide)

end Toy.SendSync
