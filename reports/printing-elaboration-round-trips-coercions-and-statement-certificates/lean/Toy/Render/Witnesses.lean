import Toy.Render.Counterexamples

/-!
# Non-vacuity witnesses (`Toy.Render`)

For each main statement, a concrete instance satisfying all of its hypotheses,
chosen so that the instance is not degenerate (where a witness reuses a
special instance, its docstring says so).
-/

namespace Toy.Render

/-- `elabWith_ppExplicit_of_wellTyped`: `tTrunc` is well typed. -/
theorem nv_elabWith_ppExplicit_of_wellTyped : WellTyped S₀ tTrunc := wellTyped_tTrunc

/-- `elabSys_ppDefault_of_defaultRecoverable`: `↑(a - b) = z` is default-recoverable
(it contains an elided coercion and two elided type arguments). -/
theorem nv_elabSys_ppDefault_of_defaultRecoverable : DefaultRecoverable S₀ tZ :=
  defaultRecoverable_tZ

/-- `defaultRecoverable_of_elabSys_ppDefault`: the default text of `tZ` is faithful. -/
theorem nv_defaultRecoverable_of_elabSys_ppDefault : elabSys S₀ (ppDefault tZ) = some tZ :=
  elabSys_ppDefault_tZ

/-- `textual_round_trip_of_faithful` with `p = ppDefault`, `cfg = cfg0`, `t = tZ`. -/
theorem nv_textual_round_trip_of_faithful : elabWith cfg0 S₀ (ppDefault tZ) = some tZ :=
  elabSys_ppDefault_tZ

/-- `ppDefault_elabWith_of_annotationFree` with `s` the default text of `tTrunc`. -/
theorem nv_ppDefault_elabWith_of_annotationFree :
    (ppDefault tTrunc).annCount = 0 ∧ elabWith cfg0 S₀ (ppDefault tTrunc) = some tReread := by
  decide

/-- `faithful_reading_unique_and_same_denotation`: the explicit text of `tTrunc`. -/
theorem nv_faithful_reading_unique_and_same_denotation :
    Faithful cfg0 S₀ (ppExplicit tTrunc) tTrunc := faithful_ppExplicit_tTrunc

/-- `ppMin_faithful_of_wellTyped`: `tTrunc` is well typed (and its default text is
not faithful, so `ppMin` must keep annotations). -/
theorem nv_ppMin_faithful_of_wellTyped :
    WellTyped S₀ tTrunc ∧ ¬ Faithful cfg0 S₀ (ppDefault tTrunc) tTrunc :=
  ⟨wellTyped_tTrunc, not_faithful_ppDefault_tTrunc⟩

/-- `elabSys_ppDefault_eq_some_iff_defaultRecoverable` (no hypotheses): both sides
hold on `tZ` and both fail on `tTrunc`. -/
theorem nv_elabSys_ppDefault_eq_some_iff_defaultRecoverable :
    (elabSys S₀ (ppDefault tZ) = some tZ ∧ DefaultRecoverable S₀ tZ) ∧
      (elabSys S₀ (ppDefault tTrunc) ≠ some tTrunc ∧ ¬ DefaultRecoverable S₀ tTrunc) := by
  decide

/-- `ppMin_locally_minimal_of_wellTyped`: `tTrunc` is well typed and the coercion on
`b` (position `[1, 1]`) is kept by `minMask cfg0`. -/
theorem nv_ppMin_locally_minimal_of_wellTyped :
    WellTyped S₀ tTrunc ∧ ([1, 1], AnnKind.coercion) ∈ minMask cfg0 S₀ tTrunc := by
  decide

/-- `ppMin_eq_ppDefault_of_faithful_ppDefault`: the default text of `tZ` is faithful. -/
theorem nv_ppMin_eq_ppDefault_of_faithful_ppDefault : Faithful cfg0 S₀ (ppDefault tZ) tZ :=
  elabSys_ppDefault_tZ

/-- `elabWith_eq_elabSys_of_fullyAnnotated`: the explicit text of `tTrunc` is fully
annotated, and the leaf-coercion reader reads it to a term, as the system
elaborator does. -/
theorem nv_elabWith_eq_elabSys_of_fullyAnnotated :
    (ppExplicit tTrunc).fullyAnnotated = true ∧
      elabWith cfgLeaves S₀ (ppExplicit tTrunc) = some tTrunc ∧
      elabSys S₀ (ppExplicit tTrunc) = some tTrunc := by
  decide

/-- A reader that agrees with the system elaborator on fully annotated text and
otherwise reads like the leaf-coercion configuration. -/
def eLeavesOnNonFull : Reader :=
  fun S s => if s.fullyAnnotated = true then elabSys S s else elabWith cfgLeaves S s

/-- `agreeing_reader_reads_ppExplicit`: `tTrunc` and the reader `eLeavesOnNonFull`,
which agrees with the system elaborator on fully annotated text but differs from it
on the default text `a - b = z`. -/
theorem nv_agreeing_reader_reads_ppExplicit :
    WellTyped S₀ tTrunc ∧ AgreeOnFull elabSys eLeavesOnNonFull ∧
      eLeavesOnNonFull S₀ (ppDefault tZ) ≠ elabSys S₀ (ppDefault tZ) :=
  ⟨wellTyped_tTrunc, fun _ _ hs => by simp [eLeavesOnNonFull, hs], by decide⟩

/-- `faithful_ppMask_mono`: from the single annotation "show the coercion on `b`"
(the text `a - b = a - ↑b`) to all annotations of `tTrunc`. -/
theorem nv_faithful_ppMask_mono :
    (∀ p k, maskOf [([1, 1], .coercion)] p k = true → maskOf (annPos [] tTrunc) p k = true) ∧
      Faithful cfg0 S₀ (ppMask (maskOf [([1, 1], .coercion)]) [] tTrunc) tTrunc := by
  refine ⟨?_, by decide⟩
  intro p k h
  simp only [maskOf, decide_eq_true_eq, List.mem_singleton] at h
  cases h
  decide

/-- `eval_eq_of_deltaNF_eq`: the abbreviation `P` and its body `a = b` are distinct
terms with the same δ-normal form. -/
theorem nv_eval_eq_of_deltaNF_eq :
    Tm.const 0 ≠ Tm.eq .nat vA vB ∧ deltaNF S₀ (.const 0) = deltaNF S₀ (.eq .nat vA vB) := by
  decide

/-- `elabE_sound`: the system elaborator on the default text of `tZ`. -/
theorem nv_elabE_sound : elabE cfg0 S₀ none (ppDefault tZ) = some (tZ, .prop) := by decide

/-- `elabs_coherent_of_subFree`: the default text `a + b = z` is subtraction-free and
has two distinct elaborations (`↑(a + b) = z` and `↑a + ↑b = z`). -/
theorem nv_elabs_coherent_of_subFree :
    (ppDefault tAddOp).subFree = true ∧ Elabs S₀ (ppDefault tAddOp) .prop tAddOp ∧
      Elabs S₀ (ppDefault tAddOp) .prop tAddLeaves ∧ tAddOp ≠ tAddLeaves :=
  ⟨by decide,
    .eq (τ := .int) rfl (.inl rfl) (.coeIns (.add rfl (.inl rfl) (.var rfl) (.var rfl))) (.var rfl),
    .eq (τ := .int) rfl (.inl rfl) (.add rfl (.inl rfl) (.coeIns (.var rfl)) (.coeIns (.var rfl)))
      (.var rfl),
    by decide⟩

/-- `a - b + a = z` with the subtraction annotated at `Nat` and nothing else annotated. -/
def sSubAnnMixed : Stx := .eq none (.add none (.sub (some .nat) (.var 0) (.var 1)) (.var 0)) (.var 2)

/-- `elabs_coherent_of_subAnnotated`: `sSubAnnMixed` is subtraction-annotated but
neither subtraction-free nor fully annotated, and has two distinct elaborations
(`↑(a - b) + ↑a = z` and `↑((a - b) + a) = z`). -/
theorem nv_elabs_coherent_of_subAnnotated :
    sSubAnnMixed.subAnnotated = true ∧ sSubAnnMixed.subFree = false ∧
      sSubAnnMixed.fullyAnnotated = false ∧
      Elabs S₀ sSubAnnMixed .prop
        (.eq .int (.add .int (.coe (.sub .nat vA vB)) (.coe vA)) vZ) ∧
      Elabs S₀ sSubAnnMixed .prop (.eq .int (.coe (.add .nat (.sub .nat vA vB) vA)) vZ) ∧
      Tm.eq .int (.add .int (.coe (.sub .nat vA vB)) (.coe vA)) vZ ≠
        Tm.eq .int (.coe (.add .nat (.sub .nat vA vB) vA)) vZ :=
  ⟨by decide, by decide, by decide,
    .eq (τ := .int) rfl (.inl rfl)
      (.add rfl (.inl rfl) (.coeIns (.sub rfl (.inr rfl) (.var rfl) (.var rfl)))
        (.coeIns (.var rfl)))
      (.var rfl),
    .eq (τ := .int) rfl (.inl rfl)
      (.coeIns (.add rfl (.inl rfl) (.sub rfl (.inr rfl) (.var rfl) (.var rfl)) (.var rfl)))
      (.var rfl),
    by decide⟩

/-- `elabs_coherent_of_fullyAnnotated`: `@eq Int (2 : Int) z` is fully annotated and
has two distinct elaborations (`(2 : Int) = z` and `↑(2 : Nat) = z`). -/
theorem nv_elabs_coherent_of_fullyAnnotated :
    sTwoEqZ.fullyAnnotated = true ∧
      Elabs S₀ sTwoEqZ .prop (.eq .int (.lit .int 2) vZ) ∧
      Elabs S₀ sTwoEqZ .prop (.eq .int (.coe (.lit .nat 2)) vZ) ∧
      Tm.eq .int (.lit .int 2) vZ ≠ Tm.eq .int (.coe (.lit .nat 2)) vZ :=
  ⟨by decide,
    .eq (τ := .int) rfl (.inr rfl) (.asc (.num rfl)) (.var rfl),
    .eq (τ := .int) rfl (.inr rfl) (.asc (.coeIns (.num rfl))) (.var rfl),
    by decide⟩

/-- Length overhead on the running examples: number of annotation tokens in the
default, deletion-greedy (for the system elaborator) and explicit renderings. -/
theorem annCount_overhead_examples :
    ((ppDefault tTrunc).annCount, (ppMin cfg0 S₀ tTrunc).annCount,
        (ppExplicit tTrunc).annCount) = (0, 1, 6) ∧
      ((ppDefault tZ).annCount, (ppMin cfg0 S₀ tZ).annCount, (ppExplicit tZ).annCount) =
        (0, 0, 3) ∧
      ((ppDefault tIntSub).annCount, (ppMin cfg0 S₀ tIntSub).annCount,
        (ppExplicit tIntSub).annCount) = (0, 1, 5) ∧
      ((ppDefault tNatSub).annCount, (ppMin cfg0 S₀ tNatSub).annCount,
        (ppExplicit tNatSub).annCount) = (0, 0, 5) := by
  decide

/-- Annotation counts of the deletion-greedy renderings for the leaf-coercion and
`Int`-numeral readers on the running examples `tTrunc, tZ, tIntSub, tNatSub`. -/
theorem annCount_overhead_examples_other_readers :
    ((ppMin cfgLeaves S₀ tTrunc).annCount, (ppMin cfgLeaves S₀ tZ).annCount,
      (ppMin cfgLeaves S₀ tIntSub).annCount, (ppMin cfgLeaves S₀ tNatSub).annCount) =
        (2, 1, 1, 0) ∧
      ((ppMin cfgIntNumerals S₀ tTrunc).annCount, (ppMin cfgIntNumerals S₀ tZ).annCount,
        (ppMin cfgIntNumerals S₀ tIntSub).annCount, (ppMin cfgIntNumerals S₀ tNatSub).annCount) =
        (1, 0, 0, 1) := by
  decide

end Toy.Render
