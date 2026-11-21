/-
Toy.Modality.Lattice
====================

Modalities form a lattice, implication closure is a closure operator, the
trace semantics `⟦·⟧ = den s` is antitone and turns joins into intersections,
closure does not change the semantics, and `⟦·⟧` reflects the order up to
closure (an order embedding on closed modalities).

The witness traces defined here are reused by the other modules.
-/
import Toy.Modality.Basic

namespace Toy.Modality

/-! ## Closure characterization (helper) -/

theorem closed_iff (s : Shape) (m : Mod) :
    Closed s m ↔ (m.derefWhole = true → m.derefEntry = true) ∧
      (m.derefEntry = true → m.nonnull = true) ∧ (s.alignLog = 0 → m.aligned = true) := by
  cases m with
  | mk a b c d e f g =>
    unfold Closed cl
    cases a <;> cases b <;> cases c <;> cases d <;> simp

theorem cl_has (s : Shape) (m : Mod) (a : Atom) :
    (cl s m).has a = match a with
      | .aligned => (m.aligned || s.alignLog == 0)
      | .nonnull => (m.nonnull || m.derefEntry || m.derefWhole)
      | .derefEntry => (m.derefEntry || m.derefWhole)
      | .derefWhole => m.derefWhole
      | .frozen => m.frozen
      | .unique => m.unique
      | .bounded => m.bounded := by
  cases a <;> rfl

/-! ## Witness traces -/

/-- The allocation `[base, base + size)` with id `0` (used by witnesses). -/
def wAlloc (s : Shape) (base : Nat) : Alloc := ⟨0, base, s.size⟩

/-- A trace satisfying every atom: aligned non-null address, live allocation,
no events. -/
def tStar (s : Shape) : Trace := ⟨s.align, [wAlloc s s.align], [], []⟩

/-- Misaligned (address `1`) but otherwise satisfying every atom. -/
def tMis (s : Shape) : Trace := ⟨1, [wAlloc s 1], [], []⟩

/-- The null address with no allocation and no events. -/
def tNull : Trace := ⟨0, [], [], []⟩

/-- Aligned, non-null, dangling (no allocation), no events. -/
def tDangling (s : Shape) : Trace := ⟨s.align, [], [], []⟩

/-- Live at entry, then freed through the argument during the call. -/
def tFreed (s : Shape) : Trace := ⟨s.align, [wAlloc s s.align], [.free .arg 0], []⟩

/-- Live; the argument writes its first pointee byte during the call. -/
def tArgWrite (s : Shape) : Trace := ⟨s.align, [wAlloc s s.align], [.write .arg s.align], []⟩

/-- Live; an unrelated pointer reads the first pointee byte during the call. -/
def tForeignRead (s : Shape) : Trace :=
  ⟨s.align, [wAlloc s s.align], [.read .other s.align], []⟩

/-- Live; during the call the argument writes the byte just past the pointee,
and an unrelated pointer reads that byte.  Every atom except `bounded` holds. -/
def tOutOfRange (s : Shape) : Trace :=
  ⟨s.align, [wAlloc s s.align], [.write .arg (s.align + s.size), .read .other (s.align + s.size)],
    []⟩

theorem inRange_self (s : Shape) (a : Nat) : InRange s a a := ⟨Nat.le_refl _, by
  have := s.size_pos; omega⟩

theorem dereferenceable_wAlloc (s : Shape) {a : Nat} (ha : 0 < a) (t : Trace)
    (haddr : t.addr = a) (hlive : wAlloc s a ∈ t.live) : Dereferenceable s t :=
  ⟨wAlloc s a, hlive, ha, by simp [wAlloc, haddr], by simp [wAlloc, haddr]⟩

theorem argInRange_of_no_arg_access (s : Shape) (t : Trace)
    (h : ∀ x, ¬ AccessedBy t.during .arg x) : ArgInRange s t :=
  fun x hx => absurd hx (h x)

theorem atomSat_tStar (s : Shape) (a : Atom) : atomSat s a (tStar s) := by
  have hp := s.align_pos
  cases a
  · exact align_mod_align s
  · show s.align ≠ 0; omega
  · exact dereferenceable_wAlloc s hp _ rfl (by simp [tStar])
  · refine ⟨dereferenceable_wAlloc s hp _ rfl (by simp [tStar]), ?_⟩
    intro al _ _ tg h; simp [tStar] at h
  · intro x _ ⟨tg, h⟩; simp [tStar] at h
  · intro x _ h; simp [tStar, AccessedBy] at h
  · exact argInRange_of_no_arg_access s _ (fun x => by simp [tStar, AccessedBy])

theorem den_tStar (s : Shape) (m : Mod) : den s m (tStar s) :=
  fun a _ => atomSat_tStar s a

theorem atomSat_tMis (s : Shape) (a : Atom) (ha : a ≠ .aligned) : atomSat s a (tMis s) := by
  cases a
  · exact absurd rfl ha
  · show (1 : Nat) ≠ 0; decide
  · exact dereferenceable_wAlloc s (a := 1) (by decide) _ rfl (by simp [tMis])
  · refine ⟨dereferenceable_wAlloc s (a := 1) (by decide) _ rfl (by simp [tMis]), ?_⟩
    intro al _ _ tg h; simp [tMis] at h
  · intro x _ ⟨tg, h⟩; simp [tMis] at h
  · intro x _ h; simp [tMis, AccessedBy] at h
  · exact argInRange_of_no_arg_access s _ (fun x => by simp [tMis, AccessedBy])

theorem not_atomSat_tMis_aligned (s : Shape) (h : s.alignLog ≠ 0) :
    ¬ atomSat s .aligned (tMis s) := one_mod_align_of_alignLog_ne_zero h

theorem atomSat_tNull (s : Shape) (a : Atom)
    (ha : a = .aligned ∨ a = .frozen ∨ a = .unique ∨ a = .bounded) : atomSat s a tNull := by
  rcases ha with rfl | rfl | rfl | rfl
  · exact zero_mod_align s
  · intro x _ ⟨tg, h⟩; simp [tNull] at h
  · intro x _ h; simp [tNull, AccessedBy] at h
  · exact argInRange_of_no_arg_access s _ (fun x => by simp [tNull, AccessedBy])

theorem not_dereferenceable_of_live_nil (s : Shape) (t : Trace) (h : t.live = []) :
    ¬ Dereferenceable s t := by
  rintro ⟨al, hal, _⟩; simp [h] at hal

theorem atomSat_tDangling (s : Shape) (a : Atom)
    (ha : a = .aligned ∨ a = .nonnull ∨ a = .frozen ∨ a = .unique ∨ a = .bounded) :
    atomSat s a (tDangling s) := by
  have hp := s.align_pos
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact align_mod_align s
  · show s.align ≠ 0; omega
  · intro x _ ⟨tg, h⟩; simp [tDangling] at h
  · intro x _ h; simp [tDangling, AccessedBy] at h
  · exact argInRange_of_no_arg_access s _ (fun x => by simp [tDangling, AccessedBy])

theorem atomSat_tFreed (s : Shape) (a : Atom) (ha : a ≠ .derefWhole) :
    atomSat s a (tFreed s) := by
  have hp := s.align_pos
  cases a
  · exact align_mod_align s
  · show s.align ≠ 0; omega
  · exact dereferenceable_wAlloc s hp _ rfl (by simp [tFreed])
  · exact absurd rfl ha
  · intro x _ ⟨tg, h⟩; simp [tFreed] at h
  · intro x _ h; simp [tFreed, AccessedBy] at h
  · exact argInRange_of_no_arg_access s _ (fun x => by simp [tFreed, AccessedBy])

theorem not_notFreedDuring_tFreed (s : Shape) : ¬ NotFreedDuring (tFreed s) := by
  intro h
  have hp := s.align_pos
  have hs := s.size_pos
  exact h (wAlloc s s.align) (by simp [tFreed])
    ⟨hp, by simp [wAlloc, tFreed], by simp [wAlloc, tFreed]; omega⟩ .arg (by simp [tFreed, wAlloc])

theorem argInRange_tArgWrite (s : Shape) : ArgInRange s (tArgWrite s) := by
  intro x hx
  simp [tArgWrite, AccessedBy] at hx
  subst hx
  exact inRange_self s _

theorem atomSat_tArgWrite (s : Shape) (a : Atom) (ha : a ≠ .frozen) :
    atomSat s a (tArgWrite s) := by
  have hp := s.align_pos
  cases a
  · exact align_mod_align s
  · show s.align ≠ 0; omega
  · exact dereferenceable_wAlloc s hp _ rfl (by simp [tArgWrite])
  · refine ⟨dereferenceable_wAlloc s hp _ rfl (by simp [tArgWrite]), ?_⟩
    intro al _ _ tg h; simp [tArgWrite] at h
  · exact absurd rfl ha
  · intro x _ h; simp [tArgWrite, AccessedBy] at h
  · exact argInRange_tArgWrite s

theorem not_atomSat_tArgWrite_frozen (s : Shape) : ¬ atomSat s .frozen (tArgWrite s) :=
  fun h => h s.align (inRange_self s _) ⟨.arg, by simp [tArgWrite]⟩

theorem atomSat_tForeignRead (s : Shape) (a : Atom) (ha : a ≠ .unique) :
    atomSat s a (tForeignRead s) := by
  have hp := s.align_pos
  cases a
  · exact align_mod_align s
  · show s.align ≠ 0; omega
  · exact dereferenceable_wAlloc s hp _ rfl (by simp [tForeignRead])
  · refine ⟨dereferenceable_wAlloc s hp _ rfl (by simp [tForeignRead]), ?_⟩
    intro al _ _ tg h; simp [tForeignRead] at h
  · intro x _ ⟨tg, h⟩; simp [tForeignRead] at h
  · exact absurd rfl ha
  · exact argInRange_of_no_arg_access s _ (fun x => by simp [tForeignRead, AccessedBy])

theorem not_atomSat_tForeignRead_unique (s : Shape) : ¬ atomSat s .unique (tForeignRead s) :=
  fun h => h s.align (inRange_self s _) (Or.inl (by simp [tForeignRead]))

theorem atomSat_tOutOfRange (s : Shape) (a : Atom) (ha : a ≠ .bounded) :
    atomSat s a (tOutOfRange s) := by
  have hp := s.align_pos
  cases a
  · exact align_mod_align s
  · show s.align ≠ 0; omega
  · exact dereferenceable_wAlloc s hp _ rfl (by simp [tOutOfRange])
  · refine ⟨dereferenceable_wAlloc s hp _ rfl (by simp [tOutOfRange]), ?_⟩
    intro al _ _ tg h; simp [tOutOfRange] at h
  · intro x hx ⟨tg, h⟩
    simp [tOutOfRange] at h
    obtain ⟨-, rfl⟩ := h
    exact absurd hx.2 (Nat.lt_irrefl _)
  · intro x hx h
    simp [tOutOfRange, AccessedBy] at h
    subst h
    exact absurd hx.2 (Nat.lt_irrefl _)
  · exact absurd rfl ha

theorem not_atomSat_tOutOfRange_bounded (s : Shape) :
    ¬ atomSat s .bounded (tOutOfRange s) := by
  intro h
  have := h (s.align + s.size) (Or.inr (by simp [tOutOfRange]))
  exact Nat.lt_irrefl _ this.2

/-- For every atom `a` outside the closure of `m` there is a trace in `⟦m⟧`
on which `a` fails (helper for the order-embedding result). -/
theorem exists_den_not_atomSat_of_not_has_cl (s : Shape) (m : Mod) (a : Atom)
    (h : (cl s m).has a = false) : ∃ t, den s m t ∧ ¬ atomSat s a t := by
  rw [cl_has] at h
  cases a
  · simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    refine ⟨tMis s, fun b hb => atomSat_tMis s b ?_, not_atomSat_tMis_aligned s h.2⟩
    rintro rfl; simp [Mod.has, h.1] at hb
  · simp only [Bool.or_eq_false_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨tNull, fun b hb => atomSat_tNull s b ?_, fun hn => hn rfl⟩
    cases b <;> simp_all [Mod.has]
  · simp only [Bool.or_eq_false_iff] at h
    refine ⟨tDangling s, fun b hb => atomSat_tDangling s b ?_,
      not_dereferenceable_of_live_nil s _ rfl⟩
    cases b <;> simp_all [Mod.has]
  · refine ⟨tFreed s, fun b hb => atomSat_tFreed s b ?_,
      fun hw => not_notFreedDuring_tFreed s hw.2⟩
    rintro rfl; simp [Mod.has] at hb; simp_all
  · refine ⟨tArgWrite s, fun b hb => atomSat_tArgWrite s b ?_, not_atomSat_tArgWrite_frozen s⟩
    rintro rfl; simp [Mod.has] at hb; simp_all
  · refine ⟨tForeignRead s, fun b hb => atomSat_tForeignRead s b ?_,
      not_atomSat_tForeignRead_unique s⟩
    rintro rfl; simp [Mod.has] at hb; simp_all
  · refine ⟨tOutOfRange s, fun b hb => atomSat_tOutOfRange s b ?_,
      not_atomSat_tOutOfRange_bounded s⟩
    rintro rfl; simp [Mod.has] at hb; simp_all

/-! ## Results -/

/-- **Bounded lattice of modalities.**  Inclusion `≤` is a partial order on
modalities, `Mod.inf`/`Mod.sup` are greatest lower and least upper bounds, and
`Mod.bot`/`Mod.top` are least and greatest. -/
theorem mod_bounded_lattice :
    (∀ m : Mod, m ≤ m) ∧
    (∀ m₁ m₂ m₃ : Mod, m₁ ≤ m₂ → m₂ ≤ m₃ → m₁ ≤ m₃) ∧
    (∀ m₁ m₂ : Mod, m₁ ≤ m₂ → m₂ ≤ m₁ → m₁ = m₂) ∧
    (∀ m₁ m₂ : Mod, Mod.inf m₁ m₂ ≤ m₁ ∧ Mod.inf m₁ m₂ ≤ m₂) ∧
    (∀ m m₁ m₂ : Mod, m ≤ m₁ → m ≤ m₂ → m ≤ Mod.inf m₁ m₂) ∧
    (∀ m₁ m₂ : Mod, m₁ ≤ Mod.sup m₁ m₂ ∧ m₂ ≤ Mod.sup m₁ m₂) ∧
    (∀ m m₁ m₂ : Mod, m₁ ≤ m → m₂ ≤ m → Mod.sup m₁ m₂ ≤ m) ∧
    (∀ m : Mod, Mod.bot ≤ m ∧ m ≤ Mod.top) := by
  refine ⟨fun m a h => h, fun _ _ _ h₁ h₂ a h => h₂ a (h₁ a h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m₁ m₂ h₁ h₂
    apply Mod.ext_has
    intro a
    have h1 := h₁ a; have h2 := h₂ a
    revert h1 h2
    cases m₁.has a <;> cases m₂.has a <;> simp
  · intro m₁ m₂
    exact ⟨fun a h => by simp at h; exact h.1, fun a h => by simp at h; exact h.2⟩
  · intro m m₁ m₂ h₁ h₂ a h
    simp [h₁ a h, h₂ a h]
  · intro m₁ m₂
    exact ⟨fun a h => by simp [h], fun a h => by simp [h]⟩
  · intro m m₁ m₂ h₁ h₂ a h
    simp at h
    rcases h with h | h
    · exact h₁ a h
    · exact h₂ a h
  · intro m
    exact ⟨fun a h => by simp at h, fun a _ => by simp⟩

/-- **Closed modalities form a sublattice, and `cl` is a closure operator.**
For every shape `s`: `cl s` is extensive, monotone and idempotent, its values
are closed, and closed modalities are closed under `Mod.inf` and `Mod.sup` and
contain `Mod.top` and `cl s Mod.bot`. -/
theorem cl_closure_operator_and_closed_sublattice (s : Shape) :
    (∀ m, m ≤ cl s m) ∧
    (∀ m₁ m₂, m₁ ≤ m₂ → cl s m₁ ≤ cl s m₂) ∧
    (∀ m, cl s (cl s m) = cl s m) ∧
    (∀ m, Closed s (cl s m)) ∧
    (∀ m₁ m₂, Closed s m₁ → Closed s m₂ → Closed s (Mod.inf m₁ m₂)) ∧
    (∀ m₁ m₂, Closed s m₁ → Closed s m₂ → Closed s (Mod.sup m₁ m₂)) ∧
    Closed s Mod.top ∧ Closed s (cl s Mod.bot) := by
  have hidem : ∀ m, cl s (cl s m) = cl s m := by
    intro m; cases m with
    | mk a b c d e f g => cases a <;> cases b <;> cases c <;> cases d <;> simp [cl]
  refine ⟨?_, ?_, hidem, hidem, ?_, ?_, ?_, hidem _⟩
  · intro m a h
    rw [cl_has]; cases a <;> simp_all [Mod.has]
  · intro m₁ m₂ h a ha
    have h1 := h .aligned; have h2 := h .nonnull; have h3 := h .derefEntry
    have h4 := h .derefWhole; have h5 := h .frozen; have h6 := h .unique
    have h7 := h .bounded
    rw [cl_has] at ha ⊢
    simp only [Mod.has] at h1 h2 h3 h4 h5 h6 h7
    cases a <;> simp only [Bool.or_eq_true] at ha ⊢
    · rcases ha with ha | ha
      · exact Or.inl (h1 ha)
      · exact Or.inr ha
    · rcases ha with (ha | ha) | ha
      · exact Or.inl (Or.inl (h2 ha))
      · exact Or.inl (Or.inr (h3 ha))
      · exact Or.inr (h4 ha)
    · rcases ha with ha | ha
      · exact Or.inl (h3 ha)
      · exact Or.inr (h4 ha)
    · exact h4 ha
    · exact h5 ha
    · exact h6 ha
    · exact h7 ha
  · intro m₁ m₂ h₁ h₂
    rw [closed_iff] at h₁ h₂ ⊢
    simp only [Mod.inf, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact ⟨h₁.1 h.1, h₂.1 h.2⟩
    · intro h; exact ⟨h₁.2.1 h.1, h₂.2.1 h.2⟩
    · intro h; exact ⟨h₁.2.2 h, h₂.2.2 h⟩
  · intro m₁ m₂ h₁ h₂
    rw [closed_iff] at h₁ h₂ ⊢
    simp only [Mod.sup, Bool.or_eq_true]
    refine ⟨?_, ?_, ?_⟩
    · rintro (h | h)
      · exact Or.inl (h₁.1 h)
      · exact Or.inr (h₂.1 h)
    · rintro (h | h)
      · exact Or.inl (h₁.2.1 h)
      · exact Or.inr (h₂.2.1 h)
    · intro h; exact Or.inl (h₁.2.2 h)
  · rfl

/-- **Antitonicity of the trace semantics.**  If `m₁ ≤ m₂` (`m₂` has every atom
of `m₁`) and `t ∈ ⟦m₂⟧`, then `t ∈ ⟦m₁⟧`. -/
theorem den_antitone (s : Shape) {m₁ m₂ : Mod} (h : m₁ ≤ m₂) (t : Trace)
    (ht : den s m₂ t) : den s m₁ t :=
  fun a ha => ht a (h a ha)

/-- **Joins become intersections.**  `⟦m₁ ⊔ m₂⟧ = ⟦m₁⟧ ∩ ⟦m₂⟧`. -/
theorem den_sup_iff (s : Shape) (m₁ m₂ : Mod) (t : Trace) :
    den s (Mod.sup m₁ m₂) t ↔ den s m₁ t ∧ den s m₂ t := by
  constructor
  · intro h
    exact ⟨den_antitone s (mod_bounded_lattice.2.2.2.2.2.1 m₁ m₂).1 t h,
      den_antitone s (mod_bounded_lattice.2.2.2.2.2.1 m₁ m₂).2 t h⟩
  · rintro ⟨h₁, h₂⟩ a ha
    simp at ha
    rcases ha with ha | ha
    · exact h₁ a ha
    · exact h₂ a ha

/-- **Closure does not change the semantics.**  `⟦cl s m⟧ = ⟦m⟧`: the atoms added
by closure (`derefEntry` from `derefWhole`; `nonnull` from either deref atom;
`aligned` when the alignment is `1`) hold on every trace of `⟦m⟧`. -/
theorem den_cl_iff (s : Shape) (m : Mod) (t : Trace) : den s (cl s m) t ↔ den s m t := by
  constructor
  · exact den_antitone s ((cl_closure_operator_and_closed_sublattice s).1 m) t
  · intro h
    rw [den_iff] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    have hd : m.derefEntry = true ∨ m.derefWhole = true → Dereferenceable s t := by
      rintro (h | h)
      · exact h3 h
      · exact (h4 h).1
    refine ⟨?_, ?_, ?_, h4, h5, h6, h7⟩
    · intro ha
      simp only [cl, Bool.or_eq_true, beq_iff_eq] at ha
      rcases ha with ha | ha
      · exact h1 ha
      · exact mod_align_of_alignLog_eq_zero ha _
    · intro hn
      simp only [cl, Bool.or_eq_true] at hn
      rcases hn with (hn | hn) | hn
      · exact h2 hn
      · exact ne_zero_of_dereferenceable (hd (Or.inl hn))
      · exact ne_zero_of_dereferenceable (hd (Or.inr hn))
    · intro he
      simp only [cl, Bool.or_eq_true] at he
      exact hd he

/-- **Order embedding up to closure.**  For every shape `s` and modalities
`m₁ m₂`: every trace of `⟦m₁⟧` is in `⟦m₂⟧` iff `m₂ ≤ cl s m₁`. -/
theorem den_subset_iff_le_cl (s : Shape) (m₁ m₂ : Mod) :
    (∀ t, den s m₁ t → den s m₂ t) ↔ m₂ ≤ cl s m₁ := by
  constructor
  · intro h a ha
    cases hc : (cl s m₁).has a
    · obtain ⟨t, ht, hna⟩ := exists_den_not_atomSat_of_not_has_cl s m₁ a hc
      exact absurd ((h t ht) a ha) hna
    · rfl
  · intro h t ht
    exact den_antitone s h t ((den_cl_iff s m₁ t).2 ht)

/-- **Order embedding on closed modalities.**  If `m₁` is closed for `s`, then
`⟦m₁⟧ ⊆ ⟦m₂⟧` iff `m₂ ≤ m₁`. -/
theorem den_subset_iff_le_of_closed (s : Shape) {m₁ : Mod} (h : Closed s m₁) (m₂ : Mod) :
    (∀ t, den s m₁ t → den s m₂ t) ↔ m₂ ≤ m₁ := by
  have := den_subset_iff_le_cl s m₁ m₂
  rw [h] at this
  exact this

/-- Semantic equality determines the closure: if `⟦m₁⟧ = ⟦m₂⟧` then
`cl s m₁ = cl s m₂`. -/
theorem cl_eq_of_den_iff (s : Shape) {m₁ m₂ : Mod} (h : ∀ t, den s m₁ t ↔ den s m₂ t) :
    cl s m₁ = cl s m₂ := by
  have hc := cl_closure_operator_and_closed_sublattice s
  have h12 : m₂ ≤ cl s m₁ := (den_subset_iff_le_cl s m₁ m₂).1 (fun t ht => (h t).1 ht)
  have h21 : m₁ ≤ cl s m₂ := (den_subset_iff_le_cl s m₂ m₁).1 (fun t ht => (h t).2 ht)
  apply mod_bounded_lattice.2.2.1
  · have := hc.2.1 _ _ h21; rw [hc.2.2.1] at this; exact this
  · have := hc.2.1 _ _ h12; rw [hc.2.2.1] at this; exact this

end Toy.Modality
