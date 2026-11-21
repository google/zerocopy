import PanicSafety.RetainResults

/-!
# Leak-freedom of the back-shift guard without the entry invariant

`guardRetain_unwound_leakFree` assumes `Inv m`. The conclusion `LeakFree m m'` also holds
without that hypothesis (`guardRetain_unwound_leakFree_noInv`), so `Inv m` is not needed for
the implication itself. Off `Inv`, however, `LeakFree` is a weak property: a value already in
the entry drop log, or one of two copies of a duplicated value, satisfies it trivially, so the
statement without `Inv m` does not express "no element is lost".
-/

namespace Toy.PanicSafety

private theorem lfni_mem_toks_iff (cs : List Cell) (t : Tok) :
    t ∈ toks cs ↔ some t ∈ cs := by
  induction cs with
  | nil => simp [toks]
  | cons c cs ih =>
    cases c with
    | none => simp [toks]
    | some u =>
      simp only [toks_cons_some, List.mem_cons, Option.some.injEq, ih]

private theorem lfni_mem_toks_take_iff (b : List Cell) (l : Nat) (t : Tok) :
    t ∈ toks (b.take l) ↔ ∃ i, i < l ∧ b[i]? = some (some t) := by
  rw [lfni_mem_toks_iff, List.mem_iff_getElem?]
  constructor
  · rintro ⟨i, hi⟩
    rw [List.getElem?_take] at hi
    split at hi
    · exact ⟨i, ‹_›, hi⟩
    · cases hi
  · rintro ⟨i, hil, hbi⟩
    refine ⟨i, ?_⟩
    rw [List.getElem?_take, ite_eq_left hil, hbi]

private theorem lfni_copyRange_getElem?_shift (c : Nat) (b : List Cell) (s d k : Nat)
    (hds : d ≤ s) (hk : k < c) (hsk : s + k < b.length) :
    (copyRange c b s d)[d + k]? = b[s + k]? := by
  induction c generalizing b s d k with
  | zero => omega
  | succ c ih =>
    rw [copyRange]
    cases k with
    | zero =>
      rw [grd_copyRange_getElem?_lt _ _ _ _ _ (by omega), Nat.add_zero, Nat.add_zero,
        List.getElem?_set_self (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    | succ k =>
      have h1 : d + (k + 1) = (d + 1) + k := by omega
      have h2 : s + (k + 1) = (s + 1) + k := by omega
      rw [h1, ih _ _ _ _ (by omega) (by omega) (by rw [List.length_set]; omega), ← h2,
        List.getElem?_set_ne (by omega)]

/-- Loop lemma: a value that is in the drop log, in a kept cell below `p - d`, or in an
unprocessed cell `[p, n)` ends up in the drop log or among the first `len` cells of the
unwound state. No invariant on the state is assumed. -/
private theorem lfni_loop (cb : Callback) (dt : DtorTable) (n : Nat) (t : Tok) :
    ∀ (r p d : Nat) (m m' : Mem),
      d ≤ p → p + r = n →
      (t ∈ m.dropped ∨
        (∃ i, i < p - d ∧ m.buf[i]? = some (some t)) ∨
        (∃ i, p ≤ i ∧ i < n ∧ m.buf[i]? = some (some t))) →
      (exec .unwind cb dt (guardLoop n r p d) p [.guard (backshift p d n)] m).1 = .unwound m' →
      t ∈ m'.dropped ∨ t ∈ toks m'.elems := by
  intro r
  induction r with
  | zero =>
    intro p d m m' _ _ _ hex
    simp [guardLoop, exec] at hex
  | succ r ih =>
    intro p d m m' hdp hpr hinv hex
    simp only [guardLoop, exec] at hex
    cases hcb : cb p with
    | panic =>
      simp only [hcb, panicFrom, unwindEntries, backshift] at hex
      cases hex
      rcases hinv with hdrop | ⟨i, hi, hbi⟩ | ⟨i, hpi, hin, hbi⟩
      · exact Or.inl hdrop
      · right
        rw [Mem.elems, lfni_mem_toks_take_iff]
        refine ⟨i, by dsimp only; omega, ?_⟩
        rw [grd_copyRange_getElem?_lt _ _ _ _ _ hi]
        exact hbi
      · right
        rw [Mem.elems, lfni_mem_toks_take_iff]
        have hib : i < m.buf.length := by
          cases h : m.buf[i]? with
          | none => rw [h] at hbi; cases hbi
          | some _ => exact (List.getElem?_eq_some_iff.mp h).1
        obtain ⟨k, rfl⟩ : ∃ k, i = p + k := ⟨i - p, by omega⟩
        refine ⟨(p - d) + k, by dsimp only; omega, ?_⟩
        rw [lfni_copyRange_getElem?_shift _ _ _ _ _ (by omega) (by omega) (by omega)]
        exact hbi
    | ret b =>
      cases b with
      | true =>
        simp only [hcb, ite_true] at hex
        by_cases hd0 : 0 < d
        · simp only [hd0, ite_true, exec] at hex
          split at hex
          · rename_i hlt
            apply ih (p + 1) d _ m' (by omega) (by omega) _ hex
            rcases hinv with hdrop | ⟨i, hi, hbi⟩ | ⟨i, hpi, hin, hbi⟩
            · exact Or.inl hdrop
            · right; left
              refine ⟨i, by omega, ?_⟩
              rw [List.getElem?_set_ne (by omega)]
              exact hbi
            · by_cases hip : i = p
              · subst i
                right; left
                refine ⟨p - d, by omega, ?_⟩
                rw [List.getElem?_set_self (by omega), List.getD_eq_getElem?_getD, hbi]
                rfl
              · right; right
                refine ⟨i, by omega, hin, ?_⟩
                rw [List.getElem?_set_ne (by omega)]
                exact hbi
          · cases hex
        · simp only [hd0, ite_false, exec] at hex
          apply ih (p + 1) d m m' (by omega) (by omega) _ hex
          rcases hinv with hdrop | ⟨i, hi, hbi⟩ | ⟨i, hpi, hin, hbi⟩
          · exact Or.inl hdrop
          · right; left; exact ⟨i, by omega, hbi⟩
          · by_cases hip : i = p
            · subst i; right; left; exact ⟨p, by omega, hbi⟩
            · right; right; exact ⟨i, by omega, hin, hbi⟩
      | false =>
        simp only [hcb, Bool.false_eq_true, ite_false, exec] at hex
        cases hbp : m.buf[p]? with
        | none => simp [hbp] at hex
        | some c =>
          cases c with
          | none => simp [hbp] at hex
          | some u =>
            simp only [hbp] at hex
            by_cases hu : u ∈ m.dropped
            · simp [hu] at hex
            · simp only [hu, ite_false] at hex
              cases hdt : dt u with
              | true =>
                simp only [hdt, ite_true, panicFrom, unwindEntries, backshift] at hex
                cases hex
                rcases hinv with hdrop | ⟨i, hi, hbi⟩ | ⟨i, hpi, hin, hbi⟩
                · exact Or.inl (List.mem_cons_of_mem u hdrop)
                · right
                  rw [Mem.elems, lfni_mem_toks_take_iff]
                  refine ⟨i, by dsimp only; omega, ?_⟩
                  rw [grd_copyRange_getElem?_lt _ _ _ _ _ (by omega)]
                  exact hbi
                · by_cases hip : i = p
                  · subst i
                    rw [hbp] at hbi
                    cases hbi
                    exact Or.inl List.mem_cons_self
                  · right
                    rw [Mem.elems, lfni_mem_toks_take_iff]
                    have hib : i < m.buf.length := (List.getElem?_eq_some_iff.mp hbi).1
                    obtain ⟨k, rfl⟩ : ∃ k, i = (p + 1) + k := ⟨i - (p + 1), by omega⟩
                    refine ⟨(p + 1 - (d + 1)) + k, by dsimp only; omega, ?_⟩
                    rw [lfni_copyRange_getElem?_shift _ _ _ _ _ (by omega) (by omega) (by omega)]
                    exact hbi
              | false =>
                simp only [hdt, Bool.false_eq_true, ite_false] at hex
                apply ih (p + 1) (d + 1) _ m' (by omega) (by omega) _ hex
                rcases hinv with hdrop | ⟨i, hi, hbi⟩ | ⟨i, hpi, hin, hbi⟩
                · exact Or.inl (List.mem_cons_of_mem u hdrop)
                · right; left; exact ⟨i, by omega, hbi⟩
                · by_cases hip : i = p
                  · subst i
                    rw [hbp] at hbi
                    cases hbi
                    exact Or.inl List.mem_cons_self
                  · right; right; exact ⟨i, by omega, hin, hbi⟩

/-- `guardRetain_unwound_leakFree` without the hypothesis `Inv m`: for every entry state, if
`guardRetain` under `unwind` unwinds to `m'`, then `LeakFree m m'`. Off `Inv`, `LeakFree` does
not express "no element is lost" (see the module documentation). -/
theorem guardRetain_unwound_leakFree_noInv (cb : Callback) (dt : DtorTable) (m m' : Mem)
    (h : run .unwind cb dt guardRetain m = .unwound m') : LeakFree m m' := by
  intro t ht
  rw [Mem.elems, lfni_mem_toks_take_iff] at ht
  obtain ⟨i, hil, hbi⟩ := ht
  exact lfni_loop cb dt m.len t m.len 0 0 m m' (Nat.le_refl _) (Nat.zero_add _)
    (Or.inr (Or.inr ⟨i, Nat.zero_le _, hil, hbi⟩)) h

end Toy.PanicSafety
