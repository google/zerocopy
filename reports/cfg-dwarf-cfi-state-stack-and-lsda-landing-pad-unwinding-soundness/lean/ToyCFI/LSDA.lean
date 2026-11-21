/-!
# LSDA call-site table lookup

A toy call-site table: entries `[start, stop)` with an optional landing pad
(`none` means "this call site has no landing pad": continue unwinding).  Three
lookup outcomes are distinguished, because personality routines treat them
differently: a landing pad, an entry without landing pad, and no entry at all.
-/

namespace Toy.CFI

/-- One call-site entry: the half-open address range `[start, stop)` and an
optional landing pad. -/
structure CallSite where
  start : Nat
  stop : Nat
  lp : Option Nat
  deriving DecidableEq, Repr

/-- A call-site table. -/
abbrev LSDA := List CallSite

/-- `e.contains pc`: `pc ∈ [e.start, e.stop)` (exclusive end). -/
def CallSite.contains (e : CallSite) (pc : Nat) : Prop := e.start ≤ pc ∧ pc < e.stop

instance (e : CallSite) (pc : Nat) : Decidable (e.contains pc) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Lookup outcomes. -/
inductive LookupResult
  | landingPad (lp : Nat)
  | noLandingPad
  | notFound
  deriving DecidableEq, Repr

/-- Outcome of a matching entry. -/
def CallSite.result (e : CallSite) : LookupResult :=
  match e.lp with
  | some lp => .landingPad lp
  | none => .noLandingPad

/-- First-match linear scan. -/
def lookupFirst : LSDA → Nat → LookupResult
  | [], _ => .notFound
  | e :: es, pc => if e.contains pc then e.result else lookupFirst es pc

/-- Early-exit scan over a table sorted by start address: stop with `notFound`
at the first entry starting after `pc`. -/
def lookupScan : LSDA → Nat → LookupResult
  | [], _ => .notFound
  | e :: es, pc =>
    if pc < e.start then .notFound
    else if pc < e.stop then e.result
    else lookupScan es pc

/-- Off-by-one variant treating the end address as inclusive. -/
def lookupIncl : LSDA → Nat → LookupResult
  | [], _ => .notFound
  | e :: es, pc => if e.start ≤ pc ∧ pc ≤ e.stop then e.result else lookupIncl es pc

/-- Entries are sorted by start address. -/
def SortedByStart (t : LSDA) : Prop := t.Pairwise (fun a b => a.start ≤ b.start)

/-- Ranges of distinct table positions are disjoint. -/
def NonOverlapping (t : LSDA) : Prop :=
  t.Pairwise (fun a b => ∀ pc, ¬ (a.contains pc ∧ b.contains pc))

/-- At most one distinct entry *value* contains `pc`: any two entries containing
`pc` are equal as values.  Duplicate identical entries are therefore permitted
(`duplicate_entries_uniqueAt_not_nonOverlapping`), unlike `NonOverlapping`,
which compares distinct table positions. -/
def UniqueAt (t : LSDA) (pc : Nat) : Prop :=
  ∀ e₁ ∈ t, ∀ e₂ ∈ t, e₁.contains pc → e₂.contains pc → e₁ = e₂

/-! ## Results -/

/-- **First-match lookup returns the unique matching entry's outcome.** If at
most one distinct entry value contains `pc` and `e` is an entry containing
`pc`, then
`lookupFirst` returns `e`'s outcome (its landing pad, or "no landing pad"). -/
theorem lookupFirst_eq_result_of_uniqueAt {t : LSDA} {pc : Nat} {e : CallSite}
    (hu : UniqueAt t pc) (he : e ∈ t) (hc : e.contains pc) : lookupFirst t pc = e.result := by
  induction t with
  | nil => cases he
  | cons x xs ih =>
    simp only [lookupFirst]
    by_cases hx : x.contains pc
    · rw [if_pos hx, hu x (List.mem_cons_self) e he hx hc]
    · rw [if_neg hx]
      rcases List.mem_cons.mp he with h | h
      · subst h; exact absurd hc hx
      · exact ih (fun a ha b hb => hu a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) h

/-- **First-match lookup reports "not found" exactly when no entry contains `pc`.**
No hypothesis on the table is needed. -/
theorem lookupFirst_eq_notFound_iff (t : LSDA) (pc : Nat) :
    lookupFirst t pc = .notFound ↔ ∀ e ∈ t, ¬ e.contains pc := by
  induction t with
  | nil => simp [lookupFirst]
  | cons x xs ih =>
    simp only [lookupFirst, List.mem_cons, forall_eq_or_imp]
    by_cases hx : x.contains pc
    · rw [if_pos hx]
      constructor
      · intro h; cases hr : x.lp <;> simp [CallSite.result, hr] at h
      · rintro ⟨h, -⟩; exact absurd hx h
    · rw [if_neg hx, ih]; simp [hx]

/-- **Sorted early-exit scan returns the unique matching entry's outcome.** For a
table sorted by start address in which at most one distinct entry value
contains `pc`, the
early-exit scan returns the outcome of the entry containing `pc`. -/
theorem lookupScan_eq_result_of_sorted_uniqueAt {t : LSDA} {pc : Nat} {e : CallSite}
    (hs : SortedByStart t) (hu : UniqueAt t pc) (he : e ∈ t) (hc : e.contains pc) :
    lookupScan t pc = e.result := by
  induction t with
  | nil => cases he
  | cons x xs ih =>
    simp only [SortedByStart, List.pairwise_cons] at hs
    obtain ⟨hxs, hs'⟩ := hs
    simp only [lookupScan]
    have hstart : x.start ≤ pc := by
      rcases List.mem_cons.mp he with h | h
      · subst h; exact hc.1
      · exact Nat.le_trans (hxs e h) hc.1
    rw [if_neg (Nat.not_lt.mpr hstart)]
    by_cases hstop : pc < x.stop
    · rw [if_pos hstop, hu x (List.mem_cons_self) e he ⟨hstart, hstop⟩ hc]
    · rw [if_neg hstop]
      rcases List.mem_cons.mp he with h | h
      · subst h; exact absurd hc.2 hstop
      · exact ih hs' (fun a ha b hb => hu a (List.mem_cons_of_mem _ ha) b
          (List.mem_cons_of_mem _ hb)) h

/-- The early-exit scan reports "not found" when no entry contains `pc` (no
hypothesis on the table). -/
theorem lookupScan_eq_notFound_of_none_contains (t : LSDA) (pc : Nat)
    (h : ∀ e ∈ t, ¬ e.contains pc) : lookupScan t pc = .notFound := by
  induction t with
  | nil => rfl
  | cons x xs ih =>
    simp only [lookupScan]
    by_cases h1 : pc < x.start
    · rw [if_pos h1]
    · rw [if_neg h1]
      have : ¬ pc < x.stop := fun h2 =>
        h x List.mem_cons_self ⟨Nat.le_of_not_lt h1, h2⟩
      rw [if_neg this]
      exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- Derivation: pairwise-disjoint ranges imply uniqueness at every `pc`. -/
theorem uniqueAt_of_nonOverlapping {t : LSDA} (h : NonOverlapping t) (pc : Nat) :
    UniqueAt t pc := by
  induction t with
  | nil => intro e₁ h1; cases h1
  | cons x xs ih =>
    simp only [NonOverlapping, List.pairwise_cons] at h
    obtain ⟨hx, hxs⟩ := h
    intro e₁ h1 e₂ h2 c1 c2
    rcases List.mem_cons.mp h1 with h1' | h1' <;> rcases List.mem_cons.mp h2 with h2' | h2'
    · rw [h1', h2']
    · subst h1'; exact absurd ⟨c1, c2⟩ (hx e₂ h2' pc)
    · subst h2'; exact absurd ⟨c2, c1⟩ (hx e₁ h1' pc)
    · exact ih hxs e₁ h1' e₂ h2' c1 c2

/-! ## Counterexamples -/

/-- Overlapping table: `[0,10) ↦ 1` and `[5,15) ↦ 2`. -/
def lsdaOverlap : LSDA := [⟨0, 10, some 1⟩, ⟨5, 15, some 2⟩]

/-- Tightness of uniqueness for `lookupFirst`: with overlapping ranges, an entry
containing `pc = 7` exists whose landing pad is not the one returned. -/
theorem lookupFirst_wrong_without_uniqueAt :
    (⟨5, 15, some 2⟩ : CallSite) ∈ lsdaOverlap ∧ (⟨5, 15, some 2⟩ : CallSite).contains 7 ∧
      ¬ UniqueAt lsdaOverlap 7 ∧
      lookupFirst lsdaOverlap 7 ≠ (⟨5, 15, some 2⟩ : CallSite).result := by
  refine ⟨by decide, by decide, fun h => ?_, by decide⟩
  have := h ⟨0, 10, some 1⟩ (by decide) ⟨5, 15, some 2⟩ (by decide) (by decide) (by decide)
  cases this

/-- Ambiguity: on an overlapping table the first-match result depends on entry
order. -/
theorem lookupFirst_order_dependent_on_overlap :
    lookupFirst lsdaOverlap 7 = .landingPad 1 ∧ lookupFirst lsdaOverlap.reverse 7 = .landingPad 2 := by
  decide

/-- Tightness of uniqueness for `lookupScan` (the overlapping table is sorted). -/
theorem lookupScan_wrong_without_uniqueAt :
    SortedByStart lsdaOverlap ∧ (⟨5, 15, some 2⟩ : CallSite) ∈ lsdaOverlap ∧
      (⟨5, 15, some 2⟩ : CallSite).contains 7 ∧ ¬ UniqueAt lsdaOverlap 7 ∧
      lookupScan lsdaOverlap 7 ≠ (⟨5, 15, some 2⟩ : CallSite).result :=
  ⟨by simp [SortedByStart, lsdaOverlap], lookupFirst_wrong_without_uniqueAt.1,
    lookupFirst_wrong_without_uniqueAt.2.1, lookupFirst_wrong_without_uniqueAt.2.2.1, by decide⟩

/-- Unsorted table: `[10,20) ↦ 1` before `[0,5) ↦ 2`. -/
def lsdaUnsorted : LSDA := [⟨10, 20, some 1⟩, ⟨0, 5, some 2⟩]

/-- Tightness of sortedness for the early-exit scan: unique entry containing
`pc = 3`, but the scan stops at the first entry and reports "not found". -/
theorem lookupScan_wrong_without_sorted :
    ¬ SortedByStart lsdaUnsorted ∧ UniqueAt lsdaUnsorted 3 ∧
      (⟨0, 5, some 2⟩ : CallSite) ∈ lsdaUnsorted ∧ (⟨0, 5, some 2⟩ : CallSite).contains 3 ∧
      lookupScan lsdaUnsorted 3 = .notFound := by
  refine ⟨by simp [SortedByStart, lsdaUnsorted], ?_, by decide, by decide, by decide⟩
  intro e₁ h1 e₂ h2 c1 c2
  simp only [lsdaUnsorted, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    simp_all [CallSite.contains]

/-- Adjacent ranges `[0,4) ↦ 1` and `[4,8) ↦ 2`. -/
def lsdaAdjacent : LSDA := [⟨0, 4, some 1⟩, ⟨4, 8, some 2⟩]

theorem lsdaAdjacent_wellFormed : SortedByStart lsdaAdjacent ∧ NonOverlapping lsdaAdjacent := by
  refine ⟨by simp [SortedByStart, lsdaAdjacent], ?_⟩
  simp only [NonOverlapping, lsdaAdjacent, List.pairwise_cons, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil, and_true, CallSite.contains]
  exact ⟨fun pc h => by omega, fun _ h => h.elim⟩

/-- Off-by-one (inclusive end): on a sorted, non-overlapping table with adjacent
ranges, treating `stop` as inclusive returns the landing pad of the range
ending at `4` for a call at `4`, and reports a landing pad for a call at `8`
that no range contains. -/
theorem lookupIncl_wrong_on_adjacent_ranges :
    lookupIncl lsdaAdjacent 4 = .landingPad 1 ∧ lookupFirst lsdaAdjacent 4 = .landingPad 2 ∧
      lookupIncl lsdaAdjacent 8 = .landingPad 2 ∧ lookupFirst lsdaAdjacent 8 = .notFound := by
  decide

/-- Off-by-one (return address): a call at address `3`, the last instruction of
the range `[0,4)`, has return address `4`; looking up the return address finds
the next range's landing pad, looking up `return address - 1` finds the right
one. -/
theorem lookup_at_return_address_misses_last_call_in_range :
    lookupFirst lsdaAdjacent (3 + 1) = .landingPad 2 ∧
      lookupFirst lsdaAdjacent (3 + 1 - 1) = .landingPad 1 := by
  decide

/-- Tightness of non-overlap for `uniqueAt_of_nonOverlapping`: the overlapping
table is not `NonOverlapping`, and uniqueness fails at `pc = 7`. -/
theorem uniqueAt_fails_without_nonOverlapping :
    ¬ NonOverlapping lsdaOverlap ∧ ¬ UniqueAt lsdaOverlap 7 := by
  refine ⟨fun h => ?_, lookupFirst_wrong_without_uniqueAt.2.2.1⟩
  exact lookupFirst_wrong_without_uniqueAt.2.2.1 (uniqueAt_of_nonOverlapping h 7)

/-- `UniqueAt` compares values: a table holding the same entry twice is
`UniqueAt` at every `pc` but not `NonOverlapping`, so even
`∀ pc, UniqueAt t pc` does not imply `NonOverlapping t`. -/
theorem duplicate_entries_uniqueAt_not_nonOverlapping :
    let e : CallSite := ⟨0, 4, some 1⟩
    (∀ pc, UniqueAt [e, e] pc) ∧ ¬ NonOverlapping [e, e] := by
  intro e
  refine ⟨fun pc => ?_, ?_⟩
  · intro e₁ h1 e₂ h2 _ _
    simp at h1 h2; rw [h1, h2]
  · intro h
    simp only [NonOverlapping, List.pairwise_cons, List.mem_singleton, forall_eq] at h
    exact h.1 0 ⟨by decide, by decide⟩

/-- Tightness of membership for `lookupFirst_eq_result_of_uniqueAt` and
`lookupScan_eq_result_of_sorted_uniqueAt`: an entry containing `pc` that is not
in the (empty, sorted, unique) table; both lookups differ from its outcome. -/
theorem lookup_eq_result_fails_without_mem :
    let e : CallSite := ⟨0, 4, some 1⟩
    SortedByStart [] ∧ UniqueAt [] 0 ∧ e ∉ ([] : LSDA) ∧ e.contains 0 ∧
      lookupFirst [] 0 ≠ e.result ∧ lookupScan [] 0 ≠ e.result := by
  intro e
  refine ⟨List.Pairwise.nil, ?_, by simp, by decide, by decide, by decide⟩
  intro _ h; cases h

/-- Tightness of containment for the same two results: an entry of a sorted,
unique table that does not contain `pc = 8`; both lookups differ from its
outcome. -/
theorem lookup_eq_result_fails_without_contains :
    let e : CallSite := ⟨0, 4, some 1⟩
    SortedByStart [e] ∧ UniqueAt [e] 8 ∧ e ∈ [e] ∧ ¬ e.contains 8 ∧
      lookupFirst [e] 8 ≠ e.result ∧ lookupScan [e] 8 ≠ e.result := by
  refine ⟨by simp [SortedByStart], ?_, by simp, by decide, by decide, by decide⟩
  intro e₁ h1 e₂ h2 _ _
  simp at h1 h2; rw [h1, h2]

/-- Non-vacuity for first-match lookup: a unique containing entry. -/
theorem lookupFirst_nonvacuity :
    UniqueAt lsdaAdjacent 4 ∧ (⟨4, 8, some 2⟩ : CallSite) ∈ lsdaAdjacent ∧
      (⟨4, 8, some 2⟩ : CallSite).contains 4 ∧ lookupFirst lsdaAdjacent 4 = .landingPad 2 :=
  ⟨uniqueAt_of_nonOverlapping lsdaAdjacent_wellFormed.2 4, by decide, by decide, by decide⟩

/-- Non-vacuity for the sorted early-exit scan. -/
theorem lookupScan_nonvacuity :
    SortedByStart lsdaAdjacent ∧ UniqueAt lsdaAdjacent 4 ∧ (⟨4, 8, some 2⟩ : CallSite) ∈ lsdaAdjacent ∧
      (⟨4, 8, some 2⟩ : CallSite).contains 4 ∧ lookupScan lsdaAdjacent 4 = .landingPad 2 :=
  ⟨lsdaAdjacent_wellFormed.1, uniqueAt_of_nonOverlapping lsdaAdjacent_wellFormed.2 4, by decide,
    by decide, by decide⟩

end Toy.CFI
