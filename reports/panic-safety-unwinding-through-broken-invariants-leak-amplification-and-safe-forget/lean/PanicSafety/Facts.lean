import PanicSafety.Basic

/-!
# Basic facts: adequacy of the drop-safety predicates
-/

namespace Toy.PanicSafety

/-! ## Adequacy lemmas -/

theorem toks_cons_some (t : Tok) (cs : List Cell) : toks (some t :: cs) = t :: toks cs := rfl

theorem toks_append (a b : List Cell) : toks (a ++ b) = toks a ++ toks b := by
  simp [toks, List.filterMap_append]

theorem ownsUniquely_cons_some_iff (d : List Tok) (t : Tok) (cs : List Cell) :
    OwnsUniquely d (some t :: cs) ↔ t ∉ d ∧ OwnsUniquely (t :: d) cs := by
  simp only [OwnsUniquely, toks_cons_some, List.nodup_cons]
  constructor
  · rintro ⟨hinit, ⟨htn, hnd⟩, hd⟩
    refine ⟨hd t (List.mem_cons_self), fun c hc => hinit c (List.mem_cons_of_mem _ hc), hnd,
      fun u hu => ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨fun h => htn (h ▸ hu), hd u (List.mem_cons_of_mem _ hu)⟩
  · rintro ⟨htd, hinit, hnd, hd⟩
    refine ⟨?_, ⟨?_, hnd⟩, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp
      · exact hinit c hc
    · intro h
      exact (hd t h) List.mem_cons_self
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact htd
      · exact fun h => hd u hu (List.mem_cons_of_mem _ h)

/-- Dropping a list of cells with non-panicking destructors is UB-free exactly when the
cells are uniquely owned. -/
theorem dropCells_noPanic_ne_ub_iff (cs : List Cell) (d : List Tok) :
    dropCells noPanicDtors cs d ≠ .ub ↔ OwnsUniquely d cs := by
  induction cs generalizing d with
  | nil => simp [dropCells, OwnsUniquely, toks]
  | cons c cs ih =>
    cases c with
    | none => simp [dropCells, OwnsUniquely]
    | some t =>
      rw [ownsUniquely_cons_some_iff]
      by_cases ht : t ∈ d
      · simp [dropCells, ht]
      · simp only [dropCells, ht, ite_false, noPanicDtors, Bool.false_eq_true]
        rw [ih]
        simp

/-- `Inv` is exactly the absence of UB in the container's drop glue when no destructor
panics. -/
theorem inv_iff_containerDrop_noPanic_ne_ub (m : Mem) :
    Inv m ↔ containerDrop noPanicDtors m ≠ .ub := by
  unfold Inv containerDrop
  by_cases h : m.len ≤ m.buf.length
  · simp only [h, ite_true, true_and]
    exact (dropCells_noPanic_ne_ub_iff _ _).symm
  · simp [h]

theorem ownsUniquely_append_singleton_iff (d : List Tok) (a : List Cell) (c : Cell) :
    OwnsUniquely d (a ++ [c]) ↔ OwnsUniquely d (c :: a) := by
  have hperm : (a ++ [c]).Perm (c :: a) := List.perm_append_singleton c a
  have htperm : (toks (a ++ [c])).Perm (toks (c :: a)) := hperm.filterMap id
  simp only [OwnsUniquely]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun x hx => h1 x (hperm.mem_iff.mpr hx), htperm.nodup_iff.mp h2,
      fun t ht => h3 t (htperm.mem_iff.mpr ht)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun x hx => h1 x (hperm.mem_iff.mp hx), htperm.nodup_iff.mpr h2,
      fun t ht => h3 t (htperm.mem_iff.mp ht)⟩

/-- Popping the last element of a container that satisfies `Inv`: the cell holds a live
value, and after dropping it and decrementing `len` the invariant still holds. -/
theorem inv_pop (m : Mem) (k : Nat) (hm : Inv m) (hl : m.len = k + 1) :
    ∃ t, m.buf[k]? = some (some t) ∧ t ∉ m.dropped ∧
      Inv { m with len := k, dropped := t :: m.dropped } := by
  obtain ⟨hlen, hown⟩ := hm
  have hk : k < m.buf.length := by omega
  have htake : m.elems = m.buf.take k ++ [m.buf[k]] := by
    simp only [Mem.elems, hl]
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    rfl
  rw [htake, ownsUniquely_append_singleton_iff] at hown
  have hsome : m.buf[k] ≠ none := hown.1 _ List.mem_cons_self
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hsome
  rw [ht, ownsUniquely_cons_some_iff] at hown
  refine ⟨t, by rw [List.getElem?_eq_getElem hk, ht], hown.1, ?_, ?_⟩
  · show k ≤ m.buf.length; omega
  · exact hown.2

/-- With an empty frame, `DropSafe` is `Inv`. -/
theorem dropSafe_nil_iff_inv (m : Mem) : DropSafe [] m ↔ Inv m := by
  simp [DropSafe, applyGuards, valueToks, Inv, Mem.elems]

/-- `DropSafe` is exactly the condition under which unwinding the frame with
non-panicking destructors is UB-free and leaves the container satisfying `Inv`. -/
theorem unwindEntries_noPanic_ok_inv_iff_dropSafe (es : List Entry) (m : Mem) :
    (∃ m', unwindEntries noPanicDtors es m = .ok m' ∧ Inv m') ↔ DropSafe es m := by
  induction es generalizing m with
  | nil => simp [unwindEntries, dropSafe_nil_iff_inv]
  | cons e es ih =>
    cases e with
    | value t =>
      have hds : DropSafe (.value t :: es) m ↔ t ∉ m.dropped ∧
          DropSafe es { m with dropped := t :: m.dropped } := by
        simp only [DropSafe, applyGuards, valueToks, List.map_cons, List.cons_append]
        rw [ownsUniquely_cons_some_iff]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
        · rintro ⟨h2, h1, h3⟩; exact ⟨h1, h2, h3⟩
      rw [hds]
      by_cases ht : t ∈ m.dropped
      · simp [unwindEntries, ht]
      · simp only [unwindEntries, ht, ite_false, noPanicDtors, Bool.false_eq_true]
        rw [ih]
        simp
    | guard g =>
      simp only [unwindEntries]
      rw [ih]
      simp only [DropSafe, applyGuards, valueToks]

/-- The sites reached do not depend on the panic mode. -/
theorem exec_sites_mode_indep (cb : Callback) (dt : DtorTable) (p : Prog) (j : Nat)
    (es : List Entry) (m : Mem) :
    (exec .abort cb dt p j es m).2 = (exec .unwind cb dt p j es m).2 := by
  induction p generalizing j es m with
  | done => simp [exec]
  | getLen k ih => simp [exec, ih]
  | call k ih =>
    simp only [exec]
    split <;> simp [ih]
  | copy s d k ih =>
    simp only [exec]
    split <;> simp [ih]
  | dropCell i k ih =>
    simp only [exec]
    split
    · split
      · rfl
      · split <;> simp [ih]
    · rfl
  | setLen n k ih => simp [exec, ih]
  | readOut i k ih =>
    simp only [exec]
    split <;> simp [ih]
  | writeBack i k ih =>
    simp only [exec]
    split
    · split <;> simp [ih]
    · rfl
  | dropVal k ih =>
    simp only [exec]
    split
    · split
      · rfl
      · split <;> simp [ih]
    · rfl
  | forgetVal k ih =>
    simp only [exec]
    split <;> simp [ih]
  | pushGuard g k ih => simp [exec, ih]
  | setGuard g k ih =>
    simp only [exec]
    split <;> simp [ih]
  | popGuard k ih =>
    simp only [exec]
    split <;> simp [ih]
  | forgetGuard k ih =>
    simp only [exec]
    split <;> simp [ih]
  | bumpA k ih => simp [exec, ih]
  | bumpB k ih => simp [exec, ih]

end Toy.PanicSafety
