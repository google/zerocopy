import ToyCFI.Funcs

/-!
# Shared lemmas for the result modules
-/

namespace Toy.CFI

/-- Extract the row a correct table assigns to a reachable PC. -/
theorem TableCorrect.row_at {f : Func} {prog : List CFIInst} (h : TableCorrect f prog)
    {c : Caller} {m : Int → Int} {b k pc : Nat} {st : MState}
    (hr : Reach f c m b k st) (hpc : f.pcOf b k = some pc) :
    ∃ R, rowAt? prog pc = some R ∧ Recovers R c st := by
  obtain ⟨pc', R, hpc', hR, hrec⟩ := h c m b k st hr
  rw [hpc] at hpc'
  cases hpc'
  exact ⟨R, hR, hrec⟩

/-- A table is incorrect as soon as one reachable state at one PC is not
recovered by the row there. -/
theorem not_tableCorrect_of_bad_row {f : Func} {prog : List CFIInst}
    {c : Caller} {m : Int → Int} {b k pc : Nat} {st : MState} {R : Row}
    (hr : Reach f c m b k st) (hpc : f.pcOf b k = some pc) (hR : rowAt? prog pc = some R)
    (hbad : cfaOf R st ≠ c.cfa) : ¬ TableCorrect f prog := by
  intro h
  obtain ⟨R', hR', hrec⟩ := h.row_at hr hpc
  rw [hR] at hR'
  cases hR'
  exact hbad hrec.1

/-- Reachable states satisfy the abstract state of the inferred annotation when
it is sound. -/
theorem reach_inv_inferred {f : Func} (hs : annSoundB f (inferredAnn f) = true)
    {c : Caller} {m : Int → Int} {b k : Nat} {st : MState} (h : Reach f c m b k st) :
    ∃ A, inferredAnn f b = some A ∧ Inv (absAt f A b k) c st :=
  reach_inv_of_annSound hs h

end Toy.CFI
